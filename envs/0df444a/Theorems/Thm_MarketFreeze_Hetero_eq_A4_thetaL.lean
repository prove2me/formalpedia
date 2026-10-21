-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq_A4_thetaL
-- name    : MarketFreeze.Hetero.eq_A4_thetaL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:51.79899+00:00
-- url     : https://prove2.me/theorems/a8773324-639c-4026-a2fb-5402d6ed87f4
-- title:
--   (A3)–(A4), pp. 35–36 — the lower cutoff θL ∈ (0, θ*) is the unique root of −∆π^hom(θ) + 0.5λ(1 − θ)(X − I)
-- statement:
--   Under Assumptions 1–5, $\lambda>0$, (A1), and (A3), there is a unique lower cutoff $\theta_L\in(0,\bar\theta)$ satisfying
--
--   $$-\Delta\pi^{\mathrm{hom}}(\theta_L)+\tfrac12\lambda(1-\theta_L)(X-I)=0.$$
--
--   At this cutoff screening still has positive benchmark value. The sole-seller gain is negative below $\theta_L$ and positive above it. This cutoff marks the end of the all-screening region.
--
--   **Formalization Note** The sign pattern states the threshold consequence used by the paper without asserting its false global derivative bound.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), equations (A3)–(A4), pp. 35–36

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq_A4_thetaL (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (hA1 : CondA1 P) (hA3 : CondA3 P) :
    ∃ θL ∈ Set.Ioo 0 P.θbar, CondA4 P θL ∧ 0 < dPi P θL ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA4 P θ → θ = θL) ∧
      (∀ θ ∈ Set.Ico 0 θL,
        -dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) < 0) ∧
      (∀ θ ∈ Set.Ioc θL P.θbar,
        0 < -dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I)) := by sorry

end MarketFreeze.Hetero
