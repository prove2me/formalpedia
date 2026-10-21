-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_footnote_19_Ehom_decreasing
-- name    : MarketFreeze.Hetero.footnote_19_Ehom_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:39.324761+00:00
-- url     : https://prove2.me/theorems/c0f0c3a5-fc1e-44a2-824b-ade9c0261001
-- title:
--   Footnote 19, p. 14 — the closed-market screening equity E^hom(θ) is strictly decreasing on [0, θ̄]
-- statement:
--   Under Assumptions 1–5, the minimum equity that induces screening with the interbank market closed,
--   $$E^{hom}(\theta)=\frac{2\theta(X-I)+2c}{1-\theta}-Y(\theta),$$
--   has negative derivative at every $\theta\in[0,\bar\theta]$ and is strictly decreasing on $[0,\bar\theta]$. A higher boom probability raises the charter value faster than it raises the incentive to gamble, so less equity is needed.
--
--   **Formalization Note** This is the first half of the last sentence of footnote 19. Its second half ("$E^{hom}(0)>0$ … leads to $E^{hom}(\theta)>0$ for all $\theta\in[0,\bar\theta]$") does not follow and is false under Assumptions 1–5 alone, so it is not stated; positivity below the cutoff $\theta^*$ is part of Proposition 1.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), footnote 19, p. 14

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem footnote_19_Ehom_decreasing (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P) :
    (∀ θ ∈ Set.Icc 0 P.θbar, deriv (Ehom P) θ < 0) ∧
    StrictAntiOn (Ehom P) (Set.Icc 0 P.θbar) := by sorry

end MarketFreeze.Hetero
