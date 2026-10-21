-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_eq_B12
-- name    : InfoRegimes.MarketEq.eq_B12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:27.897749+00:00
-- url     : https://prove2.me/theorems/50b224da-4f5a-473b-b40d-0d4eea67fa18
-- title:
--   (B.12), p. 43 — under clearing, b/c = λ(1+d)/(γq^I_D) when λ > 0, and c = γq^U_D/R when λ = 0
-- statement:
--   Assume the standing assumptions, a fraction informed $\lambda(\cdot)$ with values in $[0,1]$, a conjectured variance $V_B(\cdot) > 0$, and price coefficients $(a, b, c, d, g)$ whose optimal demands clear the market at every state and realization. Let $q^I_D$ and $q^U_D$ be the expected conditional variances (B.5) computed from these coefficients and $V_B$. Then at every state $f$:
--
--   1. if $\lambda(f) > 0$, then $c(f) \neq 0$ and
--   $$\frac{b(f)}{c(f)} = \frac{\lambda(f)(1+d)}{\gamma q^I_D(f)};$$
--   2. if $\lambda(f) = 0$, then
--   $$c(f) = \frac{\gamma q^U_D(f)}{R}.$$
--
--   The ratio $b/c$ measures how much private information per unit of supply noise the price carries; it is the quantity $r$ of (B.14) that drives the recipe (B.13)–(B.18).
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 43, eq. (B.12)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem eq_B12 (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (C : PriceCoeffs P) (hC : Clears P lam VB C) (i : State P) :
    (0 < lam i → C.c i ≠ 0 ∧
        C.b i / C.c i = lam i * (1 + C.d) / (P.gam * qID P lam VB C i)) ∧
      (lam i = 0 → C.c i = P.gam * qUD P lam VB C i / P.R) := by sorry

end InfoRegimes.MarketEq
