-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_center_readable
-- name    : FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:55.367238+00:00
-- url     : https://prove2.me/theorems/7038d041-6a2a-40bc-ab8a-0baeb48cd646
-- title:
--   Centering Leaves The Closed Gradient Unchanged
-- statement:
--   This statement identifies the action of the closed weighted gradient on a centered function.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $\nu$ be log-concave with nonempty support interior, and let $m$ be an additive Haar measure. For any element $u$ of the domain of the closed weighted operator, let $\operatorname{center}_\nu u=u-\operatorname{mean}_\nu(u)$ denote its $L^2$ centering. Then
--   $$\overline{\nabla}(\operatorname{center}_\nu u)=\overline{\nabla}u.$$
--
--   The result records that constants are annihilated by the closed gradient and allows centered representatives to be substituted without changing their gradient energy.
--
--   **Formalization Note.** The centered element is accompanied by a separately constructed domain proof; equality is equality of the resulting $L^2(\nu)$ classes.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedWeightedOperator_center
--       (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
--       hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--           ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
--             center_mem_closedWeightedOperator_domain m hν hi u⟩ =
--         hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Supporting theorems: [`closedWeightedOperator_one_eq_zero`](https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf).
--
--   Previous: [`mul_norm_closedWeightedOperator_sq_le`](https://prove2.me/theorems/df1ab815-889d-4825-b09c-233d7b8156e8) · Next: [`norm_center_sq_sub_le`](https://prove2.me/theorems/7596243b-315e-4568-9444-de9ecda59015).
--
--   [Source excerpt, lines 233–238](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L233-L238) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L232-L287 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_readable
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          center_mem_closedWeightedOperator_domain m hν hi u⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u := by sorry
