-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_mul_norm_closedWeightedOperator_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:47.899014+00:00
-- url     : https://prove2.me/theorems/df1ab815-889d-4825-b09c-233d7b8156e8
-- title:
--   Curvature Estimate On The Full Operator Domain
-- statement:
--   This statement extends the curvature estimate to the full domain of the generator.
--
--   Let $V$, $\nu$, $m$, and $U$ satisfy the heat-model assumptions, with $\nu=m.\operatorname{tilted}(-U)$ and $U\in C^2$. Let $\rho\in\mathbb R$ satisfy
--   $$\rho\|v\|^2\le D^2U(x)[v,v]$$
--   for every $x,v\in V$. Then every $F\in D(A)$ satisfies
--   $$\rho\,\|\overline{\nabla}F\|^2\le\|AF\|^2,$$
--   where $A=\overline{\nabla}^{\,\dagger}\overline{\nabla}$.
--
--   The result is the operator-domain version of the curvature bound and is reusable in semigroup energy estimates.
--
--   **Formalization Note.** The domain of $A$ is represented by the domain of `adjointComp`; the inequality is real-valued and no positivity assumption on $\rho$ is included.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mul_norm_closedWeightedOperator_sq_le {ρ : ℝ}
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
--       (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
--       ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨F, F.2.2⟩‖ ^ 2 ≤
--         ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273), [`mul_norm_closedWeightedOperator_toLp_sq_le`](https://prove2.me/theorems/1216a9e9-dda9-49e5-b0a6-d2e0cf7acb3e), [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881).
--
--   Previous: [`mul_norm_closedWeightedOperator_toLp_sq_le`](https://prove2.me/theorems/1216a9e9-dda9-49e5-b0a6-d2e0cf7acb3e) · Next: [`closedWeightedOperator_center`](https://prove2.me/theorems/7038d041-6a2a-40bc-ab8a-0baeb48cd646).
--
--   [Source excerpt, lines 119–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L119-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L116-L205 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le_readable {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by sorry
