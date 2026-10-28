-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_inv_le_scale_sq_step_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq_step_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:16.927318+00:00
-- url     : https://prove2.me/theorems/f9eabf78-c00a-4ef8-a681-0262f5a3b540
-- title:
--   One-Step Scale Lower Bound
-- statement:
--   This is the one-step inequality corresponding to BKL (32).
--
--   Let $V$ be finite-dimensional, let $\nu$ be a log-concave probability measure represented as $m\mathbin{.}\mathrm{tilted}(-U)$ with $U\in C^2$, and suppose $C_P(\nu)\le C$ for $C\in[0,\infty)$. Assume also $C>0$. For any natural number $k$ and any Poisson-iterate field $h$ at level $k$, if its scale is strictly positive, then
--
--   $$C^{-1}\le \operatorname{scale}(\bar T,h)^2.$$
--
--   Here $\bar T$ is the closed unit-weight gradient operator, and the scale is the definition used for the Poisson step.
--
--   This estimate supplies the lower bound on a positive iteration scale required in the recursive symmetry and Taylor estimates.
--
--   **Formalization Note:** The theorem uses $C$ as the real coercion of an `NNReal`; the Poincaré constant is compared in `ENNReal`. The conclusion is an ordinary real inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inv_le_scale_sq_step (hCpos : 0 < C) {k : ℕ} (h : Field ν k) (hs : 0 < scale T̄ h) :
--       (C : ℝ)⁻¹ ≤ scale T̄ h ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Domain`](https://prove2.me/theorems/26613bf5-8972-4fc0-832a-ace98ef2407a).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`centered_adjointComp_bounds`](https://prove2.me/theorems/ec846df1-cd32-4ff0-8f0d-472ede37aec2), [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360), [`sum_norm_sq_compLp_innerSL`](https://prove2.me/theorems/886e463b-28f3-4769-9471-649161462a00).
--
--   [Source excerpt, lines 385–386](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Domain.lean#L385-L386) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Domain.lean#L383-L404 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Domain`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq_step`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq_step_readable (hCpos : 0 < C) {k : ℕ} (h : Field ν k) (hs : 0 < scale T̄ h) :
    (C : ℝ)⁻¹ ≤ scale T̄ h ^ 2 := by sorry
