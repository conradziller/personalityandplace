# Personality, Place, and Democratic Resilience: replication script
#
# Input files in data/ (LiV survey and IRB data, not publicly available):
#   LiV 2022 Integriert_20230404.dta, LiV2022_gew_20230616.dta, IRB_LiV.dta,
#   IRB_2002_2020_LiV_fin.dta, IRB_2021_LiV.dta, Auswertung Memo LiV.xlsx
# Tables (tables.docx) and figures (png) are written to output/.

suppressPackageStartupMessages({
  library(haven); library(dplyr); library(tidyr); library(lme4); library(readxl)
  library(survey); library(ggplot2); library(patchwork); library(officer); library(flextable)
})
dir_data <- "data"
dir_out  <- "output"
dir.create(dir_out, showWarnings = FALSE)
options(survey.lonely.psu = "adjust", width = 200)
inp <- function(f) file.path(dir_data, f)

# ---- helpers -----------------------------------------------------------------
num_clean <- function(df) {
  for (v in names(df)) if (is.numeric(df[[v]])) {
    x <- as.numeric(zap_labels(df[[v]])); x[x %in% -9:-1] <- NA; df[[v]] <- x
  }
  df
}
item_mean <- function(df, vars) { m <- rowMeans(as.matrix(df[, vars]), na.rm = TRUE); m[is.nan(m)] <- NA; m }
minmax <- function(x) { x0 <- x - min(x, na.rm = TRUE); x0 / max(x0, na.rm = TRUE) }
zs <- function(x) (x - mean(x, na.rm = TRUE)) / sd(x, na.rm = TRUE)
wm <- function(x, w) { ok <- !is.na(x) & !is.na(w); sum(x[ok] * w[ok]) / sum(w[ok]) }
wtmean_by <- function(x, w, g) {
  ok <- !is.na(x) & !is.na(w)
  out <- tapply(ifelse(ok, x * w, 0), g, sum) / tapply(ifelse(ok, w, 0), g, sum)
  as.numeric(out[as.character(g)])
}
s_le <- function(x, m) !is.na(x) & x <= m
s_gt <- function(x, m) is.na(x) | x > m
alpha_c <- function(df, vars) {
  x <- na.omit(as.matrix(df[, vars])); k <- ncol(x)
  k / (k - 1) * (1 - sum(apply(x, 2, var)) / var(rowSums(x)))
}

fit_ml <- function(f, data, re = "(1 | nei)")
  suppressMessages(lmer(as.formula(paste(f, "+", re)), data = data, REML = FALSE, control = lmerControl(calc.derivs = FALSE)))
coef_df <- function(m) {
  b <- fixef(m); se <- sqrt(diag(as.matrix(vcov(m))))
  data.frame(term = names(b), b = unname(b), se = unname(se), p = unname(2 * pnorm(-abs(b / se))), n = nobs(m))
}
find_term <- function(nms, term) {
  if (term %in% nms) return(term)
  parts <- strsplit(term, ":", fixed = TRUE)[[1]]
  perms <- function(v) if (length(v) <= 1) list(v) else
    do.call(c, lapply(seq_along(v), function(i) lapply(perms(v[-i]), function(p) c(v[i], p))))
  for (p in perms(parts)) if (paste(p, collapse = ":") %in% nms) return(paste(p, collapse = ":"))
  NA_character_
}
lc <- function(m, terms) {
  b <- fixef(m); V <- as.matrix(vcov(m)); w <- setNames(rep(0, length(b)), names(b))
  w[vapply(terms, function(t) find_term(names(b), t), "")] <- 1
  est <- sum(w * b); se <- sqrt(as.numeric(t(w) %*% V %*% w))
  c(b = est, se = se, p = 2 * pnorm(-abs(est / se)))
}
stars <- function(p) ifelse(p < .001, "***", ifelse(p < .01, "**", ifelse(p < .05, "*", "")))
f1 <- function(x) formatC(x, format = "f", digits = 1)
f2 <- function(x) formatC(x, format = "f", digits = 2)
f3 <- function(x) formatC(x, format = "f", digits = 3)
fp3 <- function(p) ifelse(p < .001, "< .001", sub("^0", "", f3(p)))
cell <- function(m, term) {
  cd <- coef_df(m); tt <- find_term(cd$term, term)
  if (is.na(tt)) return("")
  r <- cd[cd$term == tt, ]; paste0(f3(r$b), stars(r$p), " (", f3(r$se), ")")
}
reg_tab <- function(models, rows) {
  out <- do.call(rbind, lapply(names(rows), function(l) {
    t <- rows[[l]]
    c(l, vapply(seq_along(models), function(k) if (is.na(t[k])) "" else cell(models[[k]], t[k]), ""))
  }))
  out <- rbind(out, c("Observations", vapply(models, function(m) as.character(nobs(m)), "")))
  out <- as.data.frame(out, stringsAsFactors = FALSE); names(out) <- c("term", paste0("m", seq_along(models)))
  out
}
TABS <- list()
save_tab <- function(x, id) TABS[[id]] <<- x

# ---- data preparation -----------------------------------------------------------
w1  <- num_clean(read_dta(inp("LiV 2022 Integriert_20230404.dta")))
gew <- num_clean(read_dta(inp("LiV2022_gew_20230616.dta")))
d <- inner_join(w1, gew, by = "idnr")

rev5 <- function(x) 6 - x
d <- d %>% mutate(
  population   = case_when(gruppe == 1 ~ 1, gruppe %in% 2:7 ~ 0),
  geburtsland  = case_when(F53a %in% 2:11 ~ 1, F53a == 1 ~ 0),
  migrants_pop = case_when(population == 1 & geburtsland == 1 ~ 1, population == 1 & geburtsland == 0 ~ 0),
  migrants2    = case_when(population == 0 | migrants_pop %in% 1 ~ 1, population == 1 ~ 0),
  tolerant = F10c, offen = F10g, erfinderisch = rev5(F10n), respektvoll = rev5(F10b),
  friedlich = rev5(F10f), vertrauensvoll = rev5(F10h), freundschaftlich = rev5(F10l),
  rev_faul = 8 - F43h, rev_grob = 8 - F43c,
  relatives = F8a, friends = F8b, visits = F9
)
coh_items <- c("tolerant", "offen", "friedlich", "erfinderisch", "freundschaftlich", "vertrauensvoll", "respektvoll")
for (v in c("F3c", "F3d", "F3e", "F3f")) d[[paste0(v, "_rev")]] <- 6 - d[[v]]
ce_items <- c("F3c_rev", "F3d_rev", "F3e_rev", "F3f_rev", "F4a", "F4b", "F4c", "F4d", "F4f")
d$open_adj         <- item_mean(d, coh_items)
d$colleff          <- item_mean(d, ce_items)
d$colleff_cohesion <- item_mean(d, c("F4a", "F4b", "F4c", "F4d", "F4f"))
d$colleff_control  <- item_mean(d, c("F3c_rev", "F3d_rev", "F3e_rev", "F3f_rev"))
d$big5_open  <- item_mean(d, c("F43d", "F43j", "F43n"))
d$big5_con   <- item_mean(d, c("F43a", "rev_faul", "F43l"))
d$big5_agree <- item_mean(d, c("rev_grob", "F43g", "F43m"))
d$infra      <- item_mean(d, c("F2a", "F2b", "F2c", "F2d", "F2e", "F2f"))
any_foreign <- rowSums(sapply(paste0("F53c_", 2:11), function(v) d[[v]] %in% 1)) > 0
d$citizen_de <- case_when(d$F53c_1 %in% 1 ~ 1, any_foreign ~ 0)

g <- d$gemnr_quad; w <- d$dfaktfz
for (v in c("open_adj", "colleff", "colleff_cohesion", "colleff_control", "infra", "relatives", "friends", "visits"))
  d[[paste0(v, "_nei")]] <- wtmean_by(d[[v]], w, g)
d <- rename(d, openness_adj_nei = open_adj_nei)
ok <- !is.na(d$open_adj) & !is.na(w)
sumwx <- as.numeric(tapply(ifelse(ok, w * d$open_adj, 0), g, sum)[as.character(g)])
sumw  <- as.numeric(tapply(ifelse(ok, w, 0), g, sum)[as.character(g)])
d$openness_adj_nei_loo <- ifelse(ok, (sumwx - w * d$open_adj) / (sumw - w), d$openness_adj_nei)

d <- d %>% mutate(
  female = case_when(F45 == 2 ~ 1, F45 == 1 ~ 0),
  age    = ifelse(F46_alter %in% 2018, NA, F46_alter),
  unemp  = ifelse(!is.na(F49a) & F49a == 8, 1, 0),
  length = F12,
  expose = ifelse(F18a >= 25, NA, F18a)
)
s <- as.character(d$F48b__7); s[is.na(s)] <- ""
edu_s <- match(s, sort(unique(s[s != ""]), method = "radix"))
c1 <- c(7,42,50,51,74,82,83,86,87,88,95,96,101,104,105,108,109,111,112,113,114,116,139,146,167,168,169,170,177,178,182)
c2 <- c(3,4,6,8,24,25,44,45,46,47,48,49,76,77,78,79,80,81,84,85,91,92,93,94,97,99,115,119,127,128,129,130,131,140,141,
        152,155,171,172,173,174,183,186,187)
c3 <- c(5,10:15,17:23,27,29:41,43,53,55,57:73,89,90,98,100,102,103,110,117,118,120:126,133:138,144,147:151,153,154,
        156:166,179,180,181,184,185,188)
edu <- rep(NA_real_, nrow(d))
edu[(d$F48b %in% 1) | (edu_s %in% 16)]     <- 0
edu[(d$F48b %in% 2:3) | (edu_s %in% c1)]   <- 1
edu[(d$F48b %in% 4:5) | (edu_s %in% c2)]   <- 2
edu[(d$F48b %in% 6) | (edu_s %in% c3)]     <- 3
edu[edu %in% 0] <- 4
d$edu <- edu

irb_key <- num_clean(read_dta(inp("IRB_LiV.dta"))) %>% transmute(gemnr_quad = as.character(gemnr_quad), IDIRB)
irb <- num_clean(read_dta(inp("IRB_2002_2020_LiV_fin.dta"))) %>% select(IDIRB, EWWG2021, AUSG2021, MIGG2021, SGB2_GES2021)
d <- d %>% mutate(gemnr_quad = as.character(gemnr_quad)) %>%
  left_join(irb_key, by = "gemnr_quad") %>%
  left_join(irb, by = "IDIRB", na_matches = "na") %>%
  mutate(poverty21 = SGB2_GES2021 / EWWG2021, foreign21 = AUSG2021 / EWWG2021, immigration21 = MIGG2021 / EWWG2021)

d$poltrust  <- item_mean(d, c("F33_1", "F33_2", "F33_7"))
d$diversity <- item_mean(d, c("F22a", "F22b", "F22c"))
d <- d %>% mutate(dissat_dem = 12 - F34c, afd = case_when(F32 == 5 ~ 1, F32 %in% c(1:4, 6:100) ~ 0))
alphas_pre <- c(distrust = alpha_c(d, c("F33_1", "F33_2", "F33_7")), antidiv = alpha_c(d, c("F22a", "F22b", "F22c")),
                cohesion = alpha_c(d, coh_items), colleff = alpha_c(d, ce_items))

d <- d %>% filter(!is.na(ewma_abweichung) & ewma_abweichung == 0)

med_o <- median(d$big5_open, na.rm = TRUE); med_a <- median(d$big5_agree, na.rm = TRUE); med_c <- median(d$big5_con, na.rm = TRUE)
cut2 <- function(x) ifelse(is.na(x), NA, as.numeric(x >= median(x, na.rm = TRUE)))
d <- d %>% mutate(
  antidem = ifelse(!is.na(big5_open) & !is.na(big5_agree) & !is.na(big5_con), 0, NA),
  antidem = ifelse(s_le(big5_open, med_o) & s_le(big5_agree, med_a) & s_gt(big5_con, med_c), 1, antidem),
  lowopenXlowagree = as.numeric(s_le(big5_open, med_o) & s_le(big5_agree, med_a)),
  lowopenXhighcon  = as.numeric(s_le(big5_open, med_o) & s_gt(big5_con, med_c)),
  lowagreeXhighcon = as.numeric(s_le(big5_agree, med_a) & s_gt(big5_con, med_c)),
  m_lowopen = cut2(8 - big5_open), m_lowagree = cut2(8 - big5_agree), m_highcon = cut2(big5_con),
  normpoldistrust = minmax(-poltrust), normantidiv = minmax(-diversity),
  normdissat_dem = minmax(dissat_dem), normafd = minmax(afd)
)
d$APPD <- item_mean(d, c("normpoldistrust", "normantidiv", "normdissat_dem", "normafd"))
for (v in c("expose", "age", "length", "open_adj", "openness_adj_nei", "openness_adj_nei_loo", "colleff", "colleff_nei",
            "colleff_cohesion", "colleff_cohesion_nei", "colleff_control", "colleff_control_nei", "poverty21", "immigration21"))
  d[[paste0("norm", v)]] <- minmax(d[[v]])
d <- d %>% mutate(
  city  = factor(stadt, levels = 1:10, labels = c("Bremen", "Cologne", "Bochum", "Mainz", "Stuttgart",
                                                    "Karlsruhe", "Nuremberg", "Berlin", "Dresden", "Halle")),
  nei   = factor(gemnr_quad),
  edu_f = factor(edu, levels = 1:4, labels = c("Low", "Middle", "High", "Still in education"))
)

# ---- neighborhood data -------------------------------------------------------------
nb <- d %>% group_by(gemnr_quad) %>% summarise(
  city = first(city), cohesion = first(openness_adj_nei), coh_sampson = first(colleff_cohesion_nei),
  ctrl_sampson = first(colleff_control_nei), infra = first(infra_nei), relatives = first(relatives_nei),
  friends = first(friends_nei), visits = first(visits_nei), poverty = first(poverty21),
  foreign = first(foreign21), immig = first(immigration21), appd_mean = wm(APPD, dfaktfz), .groups = "drop"
) %>% mutate(density = (zs(relatives) + zs(friends) + zs(visits)) / 3)

flows <- bind_rows(
  read_dta(inp("IRB_2021_LiV.dta")) %>% transmute(IDIRB = as.numeric(IDIRB), EWWG, EZUGGES, EABGGES, HZUZGES, HWEGGES),
  tibble(IDIRB = NA_real_, EWWG = 16784, EZUGGES = 1095, EABGGES = 970, HZUZGES = 583, HWEGGES = 539)  # Marzahn-Ost (pooled unit)
)
nb <- nb %>% left_join(irb_key %>% left_join(flows, by = "IDIRB", na_matches = "na") %>%
                         transmute(gemnr_quad, turnover = (EZUGGES + EABGGES + HZUZGES + HWEGGES) / EWWG), by = "gemnr_quad") %>%
  mutate(instability = zs(turnover), highclimate = as.numeric(appd_mean > median(appd_mean)))

sso_raw <- read_excel(inp("Auswertung Memo LiV.xlsx"), sheet = "Tabelle1", .name_repair = ~ make.names(.x, unique = TRUE))
numv <- function(v) suppressWarnings(as.numeric(as.character(v)))
sso_key <- c(Q1_KO = "002_1", Q2_KO = "002_2", Q3_KO = "002_3", Q4_KO = "002_4",
             Q1_BO = "003_1", Q2_BO = "003_2", Q3_BO = "003_3", Q4_BO = "003_4")
sso_pts <- sso_raw %>%
  transmute(gemnr_quad = unname(sso_key[Nummer]), litter = numv(Müll), graffiti = numv(Grafitti),
            social = numv(Social.Disorder), noise = numv(Lärm)) %>%
  filter(!is.na(litter) | !is.na(graffiti) | !is.na(social)) %>%
  mutate(disorder_obs = rowMeans(cbind(zs(litter), zs(noise), zs(graffiti)), na.rm = TRUE))
sso <- sso_pts %>% group_by(gemnr_quad) %>% summarise(n_points = n(), sso_disorder = mean(disorder_obs, na.rm = TRUE), .groups = "drop")
nb <- nb %>% left_join(sso, by = "gemnr_quad")

d <- d %>% left_join(nb %>% select(gemnr_quad, instability, density, appd_mean, highclimate), by = "gemnr_quad") %>%
  mutate(norminstability = minmax(instability), normdensity = minmax(density), normappd_nei = minmax(appd_mean),
         normdensity_c = normdensity - mean(minmax(nb$density)),
         lowA = as.numeric(big5_agree <= median(big5_agree, na.rm = TRUE)), lowOhighC = lowopenXhighcon)

# ---- models ---------------------------------------------------------------------------
ctrl <- "normexpose + migrants2 + female + normage + edu_f + unemp + normlength + normpoverty21 + normimmigration21 + city"
ix <- "normopenness_adj_nei:antidem"
m1 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei + antidem +", ctrl), d)
m2 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem +", ctrl), d)
d$insample <- rownames(d) %in% rownames(model.frame(m2))
d <- d %>% group_by(nei) %>% mutate(open_adj_cwc = normopen_adj - mean(normopen_adj[insample], na.rm = TRUE)) %>% ungroup()

m0  <- lmer(APPD ~ 1 + (1 | nei), data = d, REML = FALSE)
vc  <- as.data.frame(VarCorr(m0)); icc <- vc$vcov[1] / sum(vc$vcov)
rs1 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei + antidem +", ctrl), d, re = "(1 + antidem || nei)")
rs2 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem +", ctrl), d, re = "(1 + antidem || nei)")
lr  <- 2 * (as.numeric(logLik(rs1)) - as.numeric(logLik(m1)))

facets <- c("m_lowopen", "m_lowagree", "m_highcon", "lowopenXlowagree", "lowopenXhighcon", "lowagreeXhighcon")
fac <- lapply(facets, function(f) list(
  a = fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei +", f, "+", ctrl), d),
  b = fit_ml(paste0("APPD ~ normopen_adj + normopenness_adj_nei * ", f, " + ", ctrl), d)))

outs <- c("normdissat_dem", "normpoldistrust", "afd", "normantidiv")
sing <- lapply(outs, function(y) list(
  a = fit_ml(paste(y, "~ normopen_adj + normopenness_adj_nei + antidem +", ctrl), d),
  b = fit_ml(paste(y, "~ normopen_adj + normopenness_adj_nei * antidem +", ctrl), d)))

ce <- list(c("normcolleff", "normcolleff_nei"), c("normcolleff_cohesion", "normcolleff_cohesion_nei"),
           c("normcolleff_control", "normcolleff_control_nei"))
cem <- lapply(ce, function(v) fit_ml(paste("APPD ~", v[1], "+", v[2], "* antidem +", ctrl), d))

m_i2 <- fit_ml(paste("APPD ~ normopen_adj * antidem + normopenness_adj_nei * antidem +", ctrl), d)
m_i4 <- fit_ml(paste("APPD ~ open_adj_cwc * antidem + normopenness_adj_nei * antidem +", ctrl), d)
m_loo <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei_loo * antidem +", ctrl), d)
m_s1 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem + norminstability +", ctrl), d)
m_s2 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem + normpoverty21 * antidem + normimmigration21 * antidem + norminstability * antidem +", ctrl), d)
m_s3 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem + normpoverty21 * antidem + norminstability +", ctrl), d)
m_s4 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei + normpoverty21 * antidem + normimmigration21 * antidem + norminstability * antidem +", ctrl), d)

m_v1 <- fit_ml(paste("APPD ~ normopen_adj * antidem +", ctrl), d)
m_v2 <- fit_ml(paste("APPD ~ normcolleff_cohesion * antidem +", ctrl), d)
m_v3 <- fit_ml(paste("APPD ~ normcolleff_control * antidem +", ctrl), d)
m_v4 <- fit_ml(paste("APPD ~ (normopen_adj + normcolleff_cohesion + normcolleff_control) * antidem +", ctrl), d)

m_a1 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei + normappd_nei * antidem +", ctrl), d)
m_a8 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem + normappd_nei * antidem +", ctrl), d)
m_a2 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem * highclimate +", ctrl), d)
m_a4 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei + normdensity * antidem +", ctrl), d)
m_a5 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem + normdensity * antidem +", ctrl), d)
m_a7 <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * antidem * normdensity_c +", ctrl), d)

m_ag  <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * lowOhighC * lowA +", ctrl), d)
m_agH <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * lowOhighC +", ctrl), d[d$lowA %in% 0, ])
m_agL <- fit_ml(paste("APPD ~ normopen_adj + normopenness_adj_nei * lowOhighC +", ctrl), d[d$lowA %in% 1, ])
n_ag <- with(d[rownames(d) %in% rownames(model.frame(m_ag)), ], table(lowOhighC, lowA))

# ---- Table 1, Table A6, Table A7 ---------------------------------------------------------------
rows_full <- list(
  "Antidemocratic risk profile" = "antidem",
  "Social cohesion (neighborhood aggregate)" = "normopenness_adj_nei",
  "Social cohesion (aggregate) x Risk profile" = ix,
  "Perceived social cohesion (individual rating)" = "normopen_adj",
  "Migration background" = "migrants2", "Gender (female)" = "female", "Age" = "normage",
  "Middle education" = "edu_fMiddle", "High education" = "edu_fHigh", "Still in education" = "edu_fStill in education",
  "Unemployed" = "unemp", "Length of residence" = "normlength", "Av. hours spent in the neighborhood" = "normexpose",
  "Poverty neighborhood" = "normpoverty21", "Migration background (neighborhood)" = "normimmigration21")
rep_rows <- function(k) lapply(rows_full, function(t) rep(t, k))
save_tab(reg_tab(list(m1, m2), rep_rows(2)), "1")
save_tab(reg_tab(list(rs1, rs2), rep_rows(2)), "A6")
t7 <- reg_tab(unlist(sing, recursive = FALSE), rep_rows(8))
save_tab(t7, "A7")

# ---- Table 2 --------------------------------------------------------------------------------
fac_lab <- c("Low openness", "Low agreeableness", "High conscientiousness", "Low openness and low agreeableness",
             "Low openness and high conscientiousness", "Low agreeableness and high conscientiousness")
t2 <- rbind(c("Ref.: Low openness, low agreeableness, high conscientiousness", cell(m1, "antidem"), cell(m2, ix)),
            do.call(rbind, lapply(seq_along(facets), function(k)
              c(fac_lab[k], cell(fac[[k]]$a, facets[k]), cell(fac[[k]]$b, paste0("normopenness_adj_nei:", facets[k]))))))
t2 <- as.data.frame(t2, stringsAsFactors = FALSE); names(t2) <- c("term", "b_personality", "b_personality_x_cohesion")
save_tab(t2, "2")

# ---- Table A8 ---------------------------------------------------------------------------------
rows_a8 <- c(list("Antidemocratic risk profile" = rep("antidem", 3),
  "Collective efficacy (neighborhood)" = c("normcolleff_nei", NA, NA),
  "Collective efficacy (neighborhood) x Risk profile" = c("normcolleff_nei:antidem", NA, NA),
  "Perceived collective efficacy" = c("normcolleff", NA, NA),
  "Social cohesion (neighborhood)" = c(NA, "normcolleff_cohesion_nei", NA),
  "Social cohesion (neighborhood) x Risk profile" = c(NA, "normcolleff_cohesion_nei:antidem", NA),
  "Perceived social cohesion" = c(NA, "normcolleff_cohesion", NA),
  "Social control (neighborhood)" = c(NA, NA, "normcolleff_control_nei"),
  "Social control (neighborhood) x Risk profile" = c(NA, NA, "normcolleff_control_nei:antidem"),
  "Perceived social control" = c(NA, NA, "normcolleff_control")), rep_rows(3)[-(1:4)])
save_tab(reg_tab(cem, rows_a8), "A8")

# ---- Table A5, Table A10, Table A11, Table A12 ----------------------------------------------------
save_tab(reg_tab(list(m_i2, m_i4, m_s1, m_s3, m_s4, m_s2), list(
  "Antidemocratic risk profile" = rep("antidem", 6),
  "Perceived social cohesion (individual rating)" = c("normopen_adj", NA, rep("normopen_adj", 4)),
  "Perceived social cohesion x Risk profile" = c("normopen_adj:antidem", rep(NA, 5)),
  "Perceived cohesion, deviation from neighborhood mean" = c(NA, "open_adj_cwc", rep(NA, 4)),
  "Deviation x Risk profile" = c(NA, "open_adj_cwc:antidem", rep(NA, 4)),
  "Social cohesion (neighborhood aggregate)" = rep("normopenness_adj_nei", 6),
  "Social cohesion (aggregate) x Risk profile" = c(ix, ix, ix, ix, NA, ix),
  "Poverty rate x Risk profile" = c(NA, NA, NA, rep("antidem:normpoverty21", 3)),
  "Share with a migration background x Risk profile" = c(NA, NA, NA, NA, rep("antidem:normimmigration21", 2)),
  "Residential turnover" = c(NA, NA, rep("norminstability", 4)),
  "Residential turnover x Risk profile" = c(NA, NA, NA, NA, rep("antidem:norminstability", 2)))), "A5")

save_tab(reg_tab(list(m_v1, m_v2, m_v3, m_v4), list(
  "Antidemocratic risk profile" = rep("antidem", 4),
  "Perceived social cohesion (adjective pairs)" = c("normopen_adj", NA, NA, "normopen_adj"),
  "Perceived social cohesion (adjective pairs) x Risk profile" = c("normopen_adj:antidem", NA, NA, "normopen_adj:antidem"),
  "Perceived social cohesion (Sampson items)" = c(NA, "normcolleff_cohesion", NA, "normcolleff_cohesion"),
  "Perceived social cohesion (Sampson items) x Risk profile" = c(NA, "normcolleff_cohesion:antidem", NA, "normcolleff_cohesion:antidem"),
  "Perceived social control (Sampson items)" = c(NA, NA, "normcolleff_control", "normcolleff_control"),
  "Perceived social control (Sampson items) x Risk profile" = c(NA, NA, "normcolleff_control:antidem", "normcolleff_control:antidem"))), "A10")

save_tab(reg_tab(list(m_a1, m_a8, m_a2, m_a4, m_a5, m_a7), list(
  "Antidemocratic risk profile" = rep("antidem", 6),
  "Social cohesion (aggregate)" = rep("normopenness_adj_nei", 6),
  "Social cohesion (aggregate) x Risk profile" = c(NA, ix, ix, NA, ix, ix),
  "Discontent climate (aggregate APPD)" = c("normappd_nei", "normappd_nei", NA, NA, NA, NA),
  "Discontent climate x Risk profile" = c("normappd_nei:antidem", "antidem:normappd_nei", NA, NA, NA, NA),
  "High discontent neighborhood" = c(NA, NA, "highclimate", NA, NA, NA),
  "High discontent x Risk profile" = c(NA, NA, "antidem:highclimate", NA, NA, NA),
  "Cohesion x High discontent" = c(NA, NA, "normopenness_adj_nei:highclimate", NA, NA, NA),
  "Cohesion x Risk profile x High discontent" = c(NA, NA, "normopenness_adj_nei:antidem:highclimate", NA, NA, NA),
  "Local network density (aggregate)" = c(NA, NA, NA, "normdensity", "normdensity", "normdensity_c"),
  "Network density x Risk profile" = c(NA, NA, NA, "normdensity:antidem", "antidem:normdensity", "antidem:normdensity_c"),
  "Cohesion x Network density" = c(NA, NA, NA, NA, NA, "normopenness_adj_nei:normdensity_c"),
  "Cohesion x Risk profile x Network density" = c(NA, NA, NA, NA, NA, "normopenness_adj_nei:antidem:normdensity_c"))), "A11")

save_tab(reg_tab(list(m_agH, m_agL, m_ag), list(
  "Low openness and high conscientiousness (LO/HC)" = rep("lowOhighC", 3),
  "Social cohesion (neighborhood aggregate)" = rep("normopenness_adj_nei", 3),
  "Social cohesion x LO/HC" = rep("normopenness_adj_nei:lowOhighC", 3),
  "Low agreeableness (LA)" = c(NA, NA, "lowA"),
  "LO/HC x LA" = c(NA, NA, "lowOhighC:lowA"),
  "Social cohesion x LA" = c(NA, NA, "normopenness_adj_nei:lowA"),
  "Social cohesion x LO/HC x LA" = c(NA, NA, "normopenness_adj_nei:lowOhighC:lowA"))), "A12")

# ---- Table A1 -------------------------------------------------------------------------------------
inkar <- tribble(
  ~city, ~foreign_off, ~male_off, ~age_off, ~abitur_off,
  "Bremen", 22.37, 49.32, 42.60, 33.84, "Cologne", 19.45, 48.62, 41.94, 41.57,
  "Bochum", 15.38, 49.11, 44.01, 37.20, "Mainz", 19.35, 48.72, 41.07, 50.68,
  "Stuttgart", 27.28, 49.78, 41.78, 41.67, "Karlsruhe", 20.01, 50.77, 42.40, 40.47,
  "Nuremberg", 25.71, 49.09, 42.95, 26.55, "Berlin", 21.86, 49.05, 42.30, 44.42,
  "Dresden", 11.05, 49.59, 42.93, 41.06, "Halle", 12.96, 48.24, 44.17, 35.15)
d <- d %>% mutate(city_c = as.character(city), one = 1, foreign_i = 100 * (1 - citizen_de),
                  male_i = ifelse(F45 %in% 1:3, 100 * as.numeric(F45 == 1), NA), age_i = age,
                  abitur_i = ifelse(F48b %in% 1:7, 100 * as.numeric(F48b == 6), NA))
ind <- c(foreign = "foreign_i", male = "male_i", age = "age_i", abitur = "abitur_i")
a1 <- bind_rows(lapply(names(ind), function(k) {
  dd <- d[!is.na(d[[ind[[k]]]]), ]
  des <- svydesign(ids = ~gemnr_quad, strata = ~city_c, weights = ~one, data = dd, nest = TRUE)
  fit <- svyglm(as.formula(paste(ind[[k]], "~ 0 + city_c")), design = des)
  b <- coef(fit); names(b) <- sub("^city_c", "", names(b)); b <- b[inkar$city]
  V <- vcov(fit); dimnames(V) <- lapply(dimnames(V), function(x) sub("^city_c", "", x)); V <- V[inkar$city, inkar$city]
  dev <- b - inkar[[paste0(k, "_off")]]
  Fst <- as.numeric(t(dev) %*% solve(V) %*% dev) / length(dev)
  data.frame(ind = k, city = inkar$city, inkar = inkar[[paste0(k, "_off")]], survey = unname(b),
             F = Fst, p = pf(Fst, length(dev), degf(des), lower.tail = FALSE))
}))
tA1 <- a1 %>% select(ind, city, inkar, survey) %>% pivot_wider(names_from = ind, values_from = c(inkar, survey))
tA1 <- bind_rows(tA1, tA1 %>% summarise(across(-city, mean)) %>% mutate(city = "Average")) %>%
  mutate(across(-city, f1))
tA1 <- as.data.frame(tA1)[, c("city", paste0(rep(c("inkar_", "survey_"), 4), rep(names(ind), each = 2)))]
ft <- a1 %>% group_by(ind) %>% summarise(F = first(F), p = first(p), .groups = "drop")
tA1 <- rbind(tA1, c("F (10, 30)", unlist(lapply(names(ind), function(k) c("", if (k == "age") "" else f2(ft$F[ft$ind == k]))))),
             c("p", unlist(lapply(names(ind), function(k) c("", if (k == "age") "" else fp3(ft$p[ft$ind == k]))))))
save_tab(tA1, "A1")
nb_s <- d %>% group_by(gemnr_quad) %>% summarise(foreign_svy = mean(1 - citizen_de, na.rm = TRUE), .groups = "drop") %>%
  left_join(nb %>% select(gemnr_quad, foreign), by = "gemnr_quad")

# ---- Table A2 ------------------------------------------------------------------------------------
icc_fun <- function(f) {
  m <- suppressMessages(lmer(as.formula(f), data = d, REML = TRUE))
  v <- as.data.frame(VarCorr(m)); tau <- v$vcov[v$grp == "nei"]; s2 <- v$vcov[v$grp == "Residual"]
  nj <- table(model.frame(m)$nei)
  c(icc = tau / (tau + s2), rel = mean(tau / (tau + s2 / nj)), n = mean(nj))
}
eco <- rbind(icc_fun("open_adj ~ 1 + (1 | nei)"), icc_fun("open_adj ~ city + (1 | nei)"),
             icc_fun("open_adj ~ city + female + age + edu_f + migrants2 + unemp + length + antidem + (1 | nei)"))
it <- t(sapply(coh_items, function(v) icc_fun(paste(v, "~ 1 + (1 | nei)"))))
tA2 <- data.frame(measure = c("Perceived social cohesion (index)", "Net of city fixed effects",
                              "Net of city and individual composition", "Single adjective items (range)"),
                  icc = c(f3(eco[, "icc"]), paste(f3(min(it[, "icc"])), "to", f3(max(it[, "icc"])))),
                  reliability = c(f2(eco[, "rel"]), paste(f2(min(it[, "rel"])), "to", f2(max(it[, "rel"])))),
                  mean_n = c(f1(eco[, "n"]), ""))
save_tab(tA2, "A2")

# ---- Table A3, Table A4 --------------------------------------------------------------------------
ei <- d[d$insample, ] %>% mutate(edu_low = as.numeric(edu_f == "Low"), edu_mid = as.numeric(edu_f == "Middle"),
                                 edu_high = as.numeric(edu_f == "High"), edu_still = as.numeric(edu_f == "Still in education"))
nbn <- nb %>% transmute(coh = minmax(cohesion), coh_s = minmax(coh_sampson), ctl_s = minmax(ctrl_sampson), pov = minmax(poverty),
                        mig = minmax(immig), turn = minmax(turnover), serv = minmax(infra), dens = minmax(density), clim = minmax(appd_mean))
IND <- c(APPD = "APPD", normpoldistrust = "Political distrust", normantidiv = "Anti-diversity attitudes",
         normdissat_dem = "Dissatisfaction with democracy", normafd = "AfD preference", antidem = "Antidemocratic risk profile",
         m_lowopen = "Low openness", m_lowagree = "Low agreeableness", m_highcon = "High conscientiousness",
         normopen_adj = "Perceived social cohesion (individual rating)",
         normcolleff_cohesion = "Perceived social cohesion, Sampson items (individual rating)",
         normcolleff_control = "Perceived social control, Sampson items (individual rating)",
         migrants2 = "Migration background", female = "Gender (female)", normage = "Age",
         edu_low = "Low education", edu_mid = "Middle education", edu_high = "High education", edu_still = "Still in education",
         unemp = "Unemployed", normlength = "Length of residence", normexpose = "Av. hours spent in the neighborhood")
NBV <- c(coh = "Social cohesion (neighborhood aggregate)", coh_s = "Social cohesion, Sampson items (aggregate)",
         ctl_s = "Social control, Sampson items (aggregate)", pov = "Poverty rate", mig = "Share with a migration background",
         turn = "Residential turnover", serv = "Local services (aggregate)", dens = "Local network density (aggregate)",
         clim = "Discontent climate (aggregate APPD)")
desc_row <- function(x, lab) { x <- x[!is.na(x)]; c(lab, length(x), f3(mean(x)), f3(sd(x)), f3(min(x)), f3(max(x))) }
tA3 <- as.data.frame(rbind(c("Panel A. Individual level", rep("", 5)),
                           do.call(rbind, lapply(names(IND), function(v) desc_row(ei[[v]], IND[[v]]))),
                           c("Panel B. Neighborhood level", rep("", 5)),
                           do.call(rbind, lapply(names(NBV), function(v) desc_row(nbn[[v]], NBV[[v]])))), stringsAsFactors = FALSE)
names(tA3) <- c("variable", "obs", "mean", "sd", "min", "max")
save_tab(tA3, "A3")
IC <- c(APPD = "APPD", normpoldistrust = "Political distrust", normantidiv = "Anti-diversity attitudes",
        normdissat_dem = "Dissatisfaction with democracy", normafd = "AfD preference", antidem = "Antidemocratic risk profile",
        normopenness_adj_nei = "Social cohesion (neighborhood aggregate)", normopen_adj = "Perceived social cohesion (individual rating)",
        normcolleff_cohesion = "Perceived social cohesion, Sampson items", normcolleff_control = "Perceived social control, Sampson items",
        migrants2 = "Migration background", female = "Gender (female)", normage = "Age", unemp = "Unemployed",
        normlength = "Length of residence", normexpose = "Av. hours spent in the neighborhood",
        normpoverty21 = "Poverty rate (neighborhood)", normimmigration21 = "Share with a migration background (neighborhood)")
corr_tab <- function(df, labs) {
  k <- length(labs); out <- matrix("", k, k)
  for (i in seq_len(k)) for (j in seq_len(i)) {
    if (i == j) { out[i, j] <- "1"; next }
    ct <- cor.test(df[[names(labs)[i]]], df[[names(labs)[j]]])
    out[i, j] <- paste0(f2(ct$estimate), ifelse(ct$p.value < .05, "*", ""))
  }
  data.frame(variable = paste0("(", seq_len(k), ") ", labs), out, stringsAsFactors = FALSE)
}
save_tab(corr_tab(ei, IC), "A4_panelA")
save_tab(corr_tab(nbn, NBV), "A4_panelB")

# ---- Table A9 -------------------------------------------------------------------------------------
char_vars <- c(poverty = "Poverty rate (SGB II, %)", turnover = "Residential turnover (moves per 100 residents)",
               immig = "Share with a migration background (%)", infra = "Local services (aggregate, 1 to 5)",
               density = "Local network density (aggregate, z)", sso_disorder = "Observed disorder (systematic observation, z)")
contrast <- function(x, low) c(diff = mean(x[low]) - mean(x[!low]), p = t.test(x[low], x[!low])$p.value,
                               ps = t.test(x[low], x[!low], var.equal = TRUE)$p.value)
char <- bind_rows(lapply(c("cohesion", "coh_sampson", "ctrl_sampson"), function(meas) bind_rows(lapply(names(char_vars), function(v) {
  ok <- !is.na(nb[[v]]); m <- nb[[meas]][ok]; q <- quantile(m, c(1/3, 2/3))
  x <- nb[[v]][ok] * ifelse(v %in% c("poverty", "turnover", "immig"), 100, 1)
  a <- contrast(x, m <= median(m)); b <- contrast(x, m <= q[1]); c <- contrast(x, !(m > q[2]))
  data.frame(measure = meas, var = v, characteristic = char_vars[[v]], n = sum(ok),
             d_median = a[["diff"]], p_median = a[["p"]], d_lowest = b[["diff"]], p_lowest = b[["p"]],
             d_highest = c[["diff"]], p_highest = c[["p"]], ps_median = a[["ps"]], ps_lowest = b[["ps"]], ps_highest = c[["ps"]])
}))))
fd <- function(v, x) ifelse(v %in% c("infra", "density", "sso_disorder"), f2(x), f1(x))
save_tab(char %>% mutate(across(c(d_median, d_lowest, d_highest), ~ fd(var, .x)), across(c(p_median, p_lowest, p_highest), fp3)) %>%
           mutate(measure = recode(measure, cohesion = "Social cohesion (adjective pairs)", coh_sampson = "Social cohesion (Sampson items)",
                                   ctrl_sampson = "Social control (Sampson items)")) %>%
           select(measure, characteristic, n, d_median, p_median, d_lowest, p_lowest, d_highest, p_highest), "A9")
n_student <- sum(c((char$p_median < .05) != (char$ps_median < .05), (char$p_lowest < .05) != (char$ps_lowest < .05),
                   (char$p_highest < .05) != (char$ps_highest < .05)))

# ---- figures ---------------------------------------------------------------------------------------
theme_ms <- theme_minimal(base_size = 10) +
  theme(panel.grid.minor = element_blank(), panel.grid.major = element_line(colour = "#e1e0d9", linewidth = 0.3),
        axis.title = element_text(colour = "#52514e", size = 9), axis.text = element_text(colour = "#52514e", size = 8.5))
b <- fixef(m2); V <- as.matrix(vcov(m2)); x <- seq(0, 1, .01)
fig1 <- data.frame(x = x, est = b["antidem"] + b[ix] * x,
                   se = sqrt(V["antidem", "antidem"] + x^2 * V[ix, ix] + 2 * x * V["antidem", ix]))
p_top <- ggplot(fig1, aes(x, est)) +
  geom_hline(yintercept = 0, colour = "#52514e", linewidth = 0.4) +
  geom_ribbon(aes(ymin = est - 1.96 * se, ymax = est + 1.96 * se), fill = "grey80", alpha = 0.7) +
  geom_line(linewidth = 0.8) +
  scale_x_continuous(limits = c(0, 1), breaks = seq(0, 1, .2), expand = expansion(mult = .01)) +
  labs(x = NULL, y = "Marginal effect of the\nantidemocratic risk profile on APPD") +
  theme_ms + theme(axis.text.x = element_blank())
p_bot <- ggplot(data.frame(x = minmax(nb$cohesion)), aes(x)) +
  geom_histogram(binwidth = 0.1, boundary = 0, fill = "grey55", colour = "white", linewidth = 0.4) +
  scale_x_continuous(limits = c(0, 1), breaks = seq(0, 1, .2), expand = expansion(mult = .01)) +
  scale_y_continuous(breaks = seq(0, 12, 4)) +
  labs(x = "Neighborhood social cohesion (aggregate, normalized 0 to 1)", y = "Neighbor-\nhoods") + theme_ms
ggsave(file.path(dir_out, "figure_1.png"), p_top / p_bot + plot_layout(heights = c(3, 1)), width = 6.3, height = 4.4, dpi = 300, bg = "white")

fa <- function(est, lab, grp) data.frame(lab = lab, grp = grp, b = est[["b"]], se = est[["se"]])
forest <- bind_rows(
  fa(lc(m2, ix), "Main model (Table 1, M2)", "Main"),
  fa(lc(m_loo, "normopenness_adj_nei_loo:antidem"), "Leave one out aggregate", "Robustness"),
  fa(lc(m_s1, ix), "Further structural control\n(residential turnover)", "Robustness"),
  fa(lc(m_a5, ix), "Two way: network density x risk as control", "Network\ndensity"),
  fa(lc(m_a7, ix), "Three way: cohesion x risk x network density\n(buffering at mean density)", "Network\ndensity"),
  fa(lc(m_a2, ix), "Low discontent neighborhoods", "Subgroups"),
  fa(lc(m_a2, c(ix, "normopenness_adj_nei:antidem:highclimate")), "High discontent neighborhoods", "Subgroups")
) %>% mutate(lo = b - 1.96 * se, hi = b + 1.96 * se, lab = factor(lab, levels = rev(lab)),
             grp = factor(grp, levels = c("Main", "Robustness", "Network\ndensity", "Subgroups")))
figA1 <- ggplot(forest, aes(b, lab)) +
  geom_vline(xintercept = 0, colour = "#52514e", linewidth = 0.4) +
  geom_vline(xintercept = forest$b[1], colour = "grey70", linetype = "dashed", linewidth = 0.35) +
  geom_linerange(aes(xmin = lo, xmax = hi), linewidth = 0.8) + geom_point(size = 2.2) +
  facet_grid(grp ~ ., scales = "free_y", space = "free_y") +
  scale_x_continuous(limits = c(-0.5, 0.3), breaks = seq(-0.5, 0.3, 0.1), labels = function(x) sprintf("%.1f", x)) +
  labs(x = "Cross-level interaction: social cohesion (aggregate) x antidemocratic risk profile", y = NULL) +
  theme_ms + theme(strip.text.y = element_text(angle = 0, hjust = 0, size = 8.5), panel.grid.major.y = element_blank())
ggsave(file.path(dir_out, "figure_A1.png"), figA1, width = 6.5, height = 3.7, dpi = 300, bg = "white")
save_tab(forest %>% transmute(lab = gsub("\n", " ", as.character(lab)), grp = gsub("\n", " ", as.character(grp)),
                               b = f3(b), se = f3(se), lo = f3(lo), hi = f3(hi)), "FA1")

# ---- tables to Word ------------------------------------------------------------------------------
TITLES <- c(
  "1" = "Table 1: Multilevel Regression Results (DV: Anti-Pluralist Political Discontent)",
  "2" = "Table 2: Tests of Personality Facets",
  "A1" = "Table A1: Sample Composition Compared with Official Statistics",
  "A2" = "Table A2: Ecometric Properties of the Aggregated Social Cohesion Measure",
  "A3" = "Table A3: Descriptive Statistics",
  "A4_panelA" = "Table A4: Pairwise Correlations, Panel A. Individual Level",
  "A4_panelB" = "Table A4: Pairwise Correlations, Panel B. Neighborhood Level",
  "A5" = "Table A5: Contextual and Structural Specifications (DV: APPD)",
  "A6" = "Table A6: Multilevel Regressions with Random Slopes",
  "A7" = "Table A7: Multilevel Regressions of Single Indicators as Outcome",
  "A8" = "Table A8: Multilevel Regressions Using Indicators of Neighborhood Collective Efficacy",
  "A9" = "Table A9: Characteristics of Neighborhoods by Level of Social Cohesion",
  "A10" = "Table A10: Individual Perceptions of the Neighborhood as Moderators (DV: APPD)",
  "A11" = "Table A11: Amplification Tests (DV: APPD)",
  "A12" = "Table A12: Neighborhood Social Cohesion and Personality Configurations by Agreeableness (DV: APPD)",
  "FA1" = "Estimates Shown in Figure A1")
HEADERS <- list(
  "1" = c("", "M1 (Direct)", "M2 (Interaction)"),
  "2" = c("", "b Personality", "b Personality x Social cohesion"),
  "A1" = c("City", paste(rep(c("INKAR", "Survey"), 4), rep(c("non-nationals (%)", "male (%)", "mean age", "univ. entrance qual. (%)"), each = 2))),
  "A2" = c("", "ICC(1)", "Reliability", "Mean n"),
  "A3" = c("Variable", "Obs", "Mean", "SD", "Min", "Max"),
  "A6" = c("", "MA1 (Direct)", "MA2 (Interaction)"),
  "A7" = c("", paste0("MA", 3:10, " ", rep(c("Dissat. democracy", "Political distrust", "AfD preference", "Anti-diversity"), each = 2),
                      rep(c(" (direct)", " (interaction)"), 4))),
  "A8" = c("", "MA11", "MA12", "MA13"),
  "A9" = c("Measure", "Characteristic", "N", "Diff. below vs. above median", "p", "Diff. lowest vs. upper terciles", "p",
           "Diff. lower terciles vs. highest", "p"),
  "A12" = c("", "(1) High agreeableness", "(2) Low agreeableness", "(3) All respondents"),
  "FA1" = c("Specification", "Group", "b", "SE", "95% CI lower", "95% CI upper"))
doc <- read_docx() %>% body_set_default_section(prop_section(page_size = page_size(orient = "landscape")))
for (id in c("1", "2", "A1", "A2", "A3", "A4_panelA", "A4_panelB", "A5", "A6", "A7", "A8", "A9", "A10", "A11", "A12", "FA1")) {
  x <- TABS[[id]]; names(x) <- paste0("c", seq_along(x))
  hd <- if (!is.null(HEADERS[[id]])) HEADERS[[id]] else c("", paste0("(", seq_len(ncol(x) - 1), ")"))
  ft <- flextable(x) %>% set_header_labels(values = setNames(as.list(hd), names(x))) %>% theme_booktabs() %>%
    font(fontname = "Times New Roman", part = "all") %>% fontsize(size = 8, part = "all") %>% bold(part = "header") %>%
    align(j = -1, align = "center", part = "all") %>% padding(padding.top = 1, padding.bottom = 1, part = "all") %>%
    autofit() %>% fit_to_width(max_width = 9.3)
  if (id == "A9") ft <- align(ft, j = 1:2, align = "left", part = "all")
  doc <- doc %>% body_add_fpar(fpar(ftext(TITLES[[id]], fp_text(font.family = "Times New Roman", font.size = 11, bold = TRUE)),
                                    fp_p = fp_par(keep_with_next = TRUE, padding.top = 12, padding.bottom = 4))) %>%
    body_add_flextable(ft, align = "left")
}
print(doc, target = file.path(dir_out, "tables.docx"))

# ---- numbers reported in the text -------------------------------------------------------------------
pr <- function(lab, est) cat(sprintf("%-62s b = %6.3f  se = %.3f  p = %.3f\n", lab, est[["b"]], est[["se"]], est[["p"]]))
nj <- table(model.frame(m1)$nei)
hi_coh <- d$insample & d$openness_adj_nei > median(nb$cohesion); lo_coh <- d$insample & d$openness_adj_nei <= median(nb$cohesion)
cat("\nData and measures\n")
cat("Medians openness, agreeableness, conscientiousness:", med_o, med_a, med_c, "\n")
cat("Risk profile: n =", sum(d$antidem %in% 1), "of", sum(!is.na(d$antidem)), sprintf("(%.1f%%)\n", 100 * mean(d$antidem, na.rm = TRUE)))
cat("Cronbach's alpha distrust / antidiversity / cohesion / collective efficacy:", f2(alphas_pre), "\n")
cat("Cronbach's alpha APPD index:", f2(alpha_c(d, c("normpoldistrust", "normantidiv", "normdissat_dem", "normafd"))), "\n")
cat("Range poverty rate (%):", f1(100 * range(nb$poverty)), " migration background (%):", f1(100 * range(nb$immig)),
    " turnover (per 100):", f1(100 * range(nb$turnover)), "\n")
cat("Systematic observation: points =", sum(sso$n_points), " mean per neighborhood =", f1(mean(sso$n_points)), "\n")
for (v in c("ctrl_sampson", "coh_sampson", "cohesion")) {
  ct <- cor.test(nb$sso_disorder, nb[[v]]); cat(sprintf("r(observed disorder, %s) = %.2f, p = %.3f\n", v, ct$estimate, ct$p.value))
}
cat("Mean residents per neighborhood (Table A2) =", f1(eco[1, "n"]), " reliability =", f2(eco[1, "rel"]), "\n")
cat("Share with risk profile, below / above median cohesion (estimation sample):",
    f1(100 * mean(d$antidem[lo_coh])), "/", f1(100 * mean(d$antidem[hi_coh])), "percent\n")
cat("\nModels\n")
cat("ICC APPD =", f3(icc), " respondents per neighborhood:", min(nj), "to", max(nj), " mean =", f1(mean(nj)), " N =", nobs(m2), "\n")
cat("LR test random slope: chi2 =", f2(lr), " p =", f3(pchisq(lr, 1, lower.tail = FALSE)), "\n")
pr("Main model: cohesion x risk", lc(m2, ix)); pr("Main model: risk at lowest cohesion", lc(m2, "antidem"))
for (k in seq_along(outs)) pr(paste("Single indicator:", outs[k]), lc(sing[[k]]$b, ix))
for (k in seq_along(ce)) pr(paste("Collective efficacy:", ce[[k]][2]), lc(cem[[k]], paste0(ce[[k]][2], ":antidem")))
pr("Joint: cohesion x risk", lc(m_i2, ix)); pr("Joint: individual rating x risk", lc(m_i2, "normopen_adj:antidem"))
pr("Group mean centered: cohesion x risk", lc(m_i4, ix)); pr("Leave one out: cohesion x risk", lc(m_loo, "normopenness_adj_nei_loo:antidem"))
pr("Individual only: adjective pairs x risk", lc(m_v1, "normopen_adj:antidem"))
pr("Individual only: Sampson cohesion x risk", lc(m_v2, "normcolleff_cohesion:antidem"))
pr("Individual only: Sampson control x risk", lc(m_v3, "normcolleff_control:antidem"))
pr("Turnover control: cohesion x risk", lc(m_s1, ix))
cat("r(cohesion, poverty) =", f2(cor(nb$cohesion, nb$poverty)), "\n")
pr("Poverty x risk without cohesion interaction", lc(m_s4, "antidem:normpoverty21"))
pr("Poverty x risk and cohesion x risk: cohesion", lc(m_s3, ix)); pr("Poverty x risk and cohesion x risk: poverty", lc(m_s3, "antidem:normpoverty21"))
pr("Climate x risk", lc(m_a1, "normappd_nei:antidem"))
pr("Climate x risk jointly with cohesion: climate", lc(m_a8, "antidem:normappd_nei")); pr("Climate x risk jointly with cohesion: cohesion", lc(m_a8, ix))
pr("Buffering, high discontent neighborhoods", lc(m_a2, c(ix, "normopenness_adj_nei:antidem:highclimate")))
pr("Buffering, low discontent neighborhoods", lc(m_a2, ix)); pr("Difference (three way term)", lc(m_a2, "normopenness_adj_nei:antidem:highclimate"))
pr("Density x risk", lc(m_a4, "normdensity:antidem")); pr("Cohesion x risk x density", lc(m_a7, "normopenness_adj_nei:antidem:normdensity_c"))
pr("Low agreeableness: cohesion x LO/HC", lc(m_agL, "normopenness_adj_nei:lowOhighC"))
pr("High agreeableness: cohesion x LO/HC", lc(m_agH, "normopenness_adj_nei:lowOhighC"))
pr("Three way: cohesion x LO/HC x LA", lc(m_ag, "normopenness_adj_nei:lowOhighC:lowA"))
cat("LO/HC respondents, low / high agreeableness:", n_ag["1", "1"], "/", n_ag["1", "0"], "\n")
cat("Table A1: r(survey share of non-nationals, register share) =", f2(cor(nb_s$foreign_svy, nb_s$foreign)), "\n")
cat("Table A9: comparisons in which Welch and Student t tests differ at p < .05:", n_student, "\n")
