-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_6_4
-- name    : OptStochMatch.Tight.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:56:52.875481+00:00
-- url     : https://prove2.me/theorems/e3690c39-b173-44df-8a10-989f4ed95518
-- title:
--   Lemma 6.4 — the balanced rule earns (1 − e^{1−e} + κ) OPT in both models
-- statement:
--   In the nontrivial cases $C=\Lambda([m])>0$ and, in the i.i.d. model, $n\ge2$, the balanced rule with exact sampling exists and has expected matching size at least $(1-e^{1-e}+\kappa)\,\mathrm{OPT}$ in the Poisson model and at least $(1-e^{1-e}+\kappa)\,\mathrm{OPT}_n$ in the i.i.d. model, where $\kappa=2^{-18}m^{-3}$.
--
--   Differences from the source:
--   - reading: 'the balanced rule with exact sampling' → existence of a balanced routing rule, and the bound for every one (any supporting type flow); reason: §6.1 asserts the allocation exists and obtains a flow by Lemma 2.3; the flow is not unique and the argument does not depend on the choice
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 6.4, p. 29 (PDF p. 30), with the nontrivial cases stated on p. 29 and κ from Lemma 6.3

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Algorithms
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 6.4 (p. 29, PDF 30), with the existence claim of §6.1. In the nontrivial cases
`C = Λ([m]) > 0` and, in the i.i.d. model, `n ≥ 2`, the balanced rule with exact sampling
(which exists) has expected matching size at least `(1 − e^{1−e} + κ) OPT` in the Poisson model
and at least `(1 − e^{1−e} + κ) OPT_n` in the i.i.d. model, `κ = 2^{−18} m^{−3}`. -/
theorem lemma_6_4 :
    (∀ (m : ℕ) (lam : Ty m → ℝ≥0), 0 < coverRate lam Finset.univ →
      (∃ ρ : RoutingRule m, IsBalancedRouting lam ρ) ∧
      ∀ ρ : RoutingRule m, IsBalancedRouting lam ρ →
        (cStar + kappa m) * optPoisModel lam ≤ algRoutePois lam ρ) ∧
    (∀ (m n : ℕ) (mu : Ty m → ℝ≥0), 2 ≤ n → ∑ S, mu S = 1 →
      0 < coverRate (iidRates n mu) Finset.univ →
      (∃ ρ : RoutingRule m, IsBalancedRouting (iidRates n mu) ρ) ∧
      ∀ ρ : RoutingRule m, IsBalancedRouting (iidRates n mu) ρ →
        (cStar + kappa m) * optIID n mu ≤ algRouteIID n mu ρ) := by sorry

end OptStochMatch.Tight
