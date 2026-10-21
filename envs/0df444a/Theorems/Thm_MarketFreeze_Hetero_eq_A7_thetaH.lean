-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq_A7_thetaH
-- name    : MarketFreeze.Hetero.eq_A7_thetaH
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:43.748309+00:00
-- url     : https://prove2.me/theorems/da026661-cc57-4fe4-a8ed-43284e5aaf46
-- title:
--   (A6)–(A7), p. 36 — the upper cutoff θH ∈ (θ*, θ̄) is the unique root of ∆π^hom(θ) + 0.5λ(1 − θ)(X − I) + ψλ(X − I)
-- statement:
--   Under Assumptions 1–5, $\lambda>0$, (A1), and the corrected endpoint condition (A6), there is a unique upper cutoff $\theta_H\in(0,\bar\theta)$ satisfying
--
--   $$\Delta\pi^{\mathrm{hom}}(\theta_H)+\tfrac12\lambda(1-\theta_H)(X-I)+\psi\lambda(X-I)=0.$$
--
--   The benchmark screening value is negative at this cutoff. The sole-buyer gain is positive below $\theta_H$ and negative above it. This cutoff marks the start of the no-screening region.
--
--   **Formalization Note** The printed (A6) has a sign error; its preceding sole-buyer deviation inequality fixes the sign used here.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), equations (A6)–(A7), p. 36

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq_A7_thetaH (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (hA1 : CondA1 P) (hA6 : CondA6 P) :
    ∃ θH ∈ Set.Ioo 0 P.θbar, CondA7 P θH ∧ dPi P θH < 0 ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA7 P θ → θ = θH) ∧
      (∀ θ ∈ Set.Ico 0 θH,
        0 < dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) +
          P.ψ * P.lam * (P.X - P.I)) ∧
      (∀ θ ∈ Set.Ioc θH P.θbar,
        dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) +
          P.ψ * P.lam * (P.X - P.I) < 0) := by sorry

end MarketFreeze.Hetero
