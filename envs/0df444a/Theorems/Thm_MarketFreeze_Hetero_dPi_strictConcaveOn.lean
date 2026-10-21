-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_dPi_strictConcaveOn
-- name    : MarketFreeze.Hetero.dPi_strictConcaveOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:49.89451+00:00
-- url     : https://prove2.me/theorems/4bf5e884-1a94-4f1f-b0ff-a7e65db94306
-- title:
--   Proof of Proposition 5, p. 41 — the second derivative of ∆π^hom is negative wherever it exists
-- statement:
--   Under Assumptions 1–5, the difference between the benchmark screening and nonscreening profits is strictly concave on the allowed boom-probability interval. At each interior point where $Y''$ exists, it also obeys the source's displayed identity and strict inequality:
--
--   $$\frac{d^2\Delta\pi^{\mathrm{hom}}}{d\theta^2}=
--   [\psi+\tfrac12(1-\theta)]Y''(\theta)-Y'(\theta)
--   -\frac{4\psi(X-I+c)}{(1-\theta)^3}<0.$$
--
--   This shape controls the number and order of the screening cutoffs.
--
--   **Formalization Note** Assumption 2 supplies concavity of $Y$ without requiring a second derivative. The derivative clause is conditional on the existence of $Y''$ at the point; the strict concavity clause remains meaningful throughout the interval. The paper's separate assertion that $\Delta\pi^{\mathrm{hom}}$ decreases globally is false under its hypotheses and is not used here.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), proof of Proposition 5, p. 41

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem dPi_strictConcaveOn (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P) :
    StrictConcaveOn ℝ (Set.Icc 0 P.θbar) (dPi P) ∧
    (∀ θ ∈ Set.Ioo 0 P.θbar, DifferentiableAt ℝ (deriv P.Y) θ →
      deriv (deriv (dPi P)) θ =
        (P.ψ + (1 / 2 : ℝ) * (1 - θ)) * deriv (deriv P.Y) θ -
          deriv P.Y θ - 4 * P.ψ * (P.X - P.I + P.c) / (1 - θ) ^ 3 ∧
      deriv (deriv (dPi P)) θ < 0) := by sorry

end MarketFreeze.Hetero
