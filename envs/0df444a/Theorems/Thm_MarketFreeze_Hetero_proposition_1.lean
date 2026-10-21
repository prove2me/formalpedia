-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_proposition_1
-- name    : MarketFreeze.Hetero.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:41.562501+00:00
-- url     : https://prove2.me/theorems/6bf0346e-0f33-443d-875d-330d45abe88d
-- title:
--   Proposition 1, p. 15 — the unique closed-market outcome screens below θ* and avoids screening at and above θ*
-- statement:
--   Under Assumptions 1–5 and the intermediate screening-cost condition (A1), there is a cutoff $\theta^*\in(0,\bar\theta)$ with $\Delta\pi^{\mathrm{hom}}(\theta^*)=0$. The unique reduced closed-market outcome screens and holds $E^{\mathrm{hom}}(\theta)>0$ below the cutoff; from the cutoff through $\bar\theta$ it does not screen and holds zero equity. The payoff comparisons are:
--
--   $$\theta<\theta^*:\ \pi_{ns}^{\mathrm{hom}}(\theta)<\pi_s^{\mathrm{hom}}(\theta),\quad E^{\mathrm{hom}}(\theta)>0;\qquad
--   \theta>\theta^*:\ \pi_s^{\mathrm{hom}}(\theta)<\pi_{ns}^{\mathrm{hom}}(\theta).$$
--
--   This is the closed-market benchmark from which the trading cutoffs are measured. **Formalization Note** The Boolean outcome and its equity amount encode the paper's payoff-based strategy characterization; at the tie $\theta^*$, footnote 21 selects no screening.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), Proposition 1, p. 15

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem proposition_1 (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hA1 : CondA1 P) :
    ∃ θs : ℝ, 0 < θs ∧ θs < P.θbar ∧ dPi P θs = 0 ∧
      (∀ θ ∈ Set.Ico 0 θs, ∀ screens : Bool, ∀ E : ℝ,
        IsClosedEquilibrium P θ screens E ↔ screens = true ∧ E = Ehom P θ) ∧
      (∀ θ ∈ Set.Icc θs P.θbar, ∀ screens : Bool, ∀ E : ℝ,
        IsClosedEquilibrium P θ screens E ↔ screens = false ∧ E = 0) ∧
      (∀ θ ∈ Set.Ico 0 θs, piNS P θ < piS P θ ∧ 0 < Ehom P θ) ∧
      (∀ θ ∈ Set.Ioc θs P.θbar, piS P θ < piNS P θ) := by sorry

end MarketFreeze.Hetero
