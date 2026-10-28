-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_literatureConstant_le_of_gap_readable
-- name    : FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:36.016983+00:00
-- url     : https://prove2.me/theorems/b49f19dd-a419-448a-a1a8-ceb4b69486a2
-- title:
--   Poincaré Constant Bounded By A Form-Domain Gap
-- statement:
--   This statement converts a form-domain Poincaré inequality into an upper bound for the intrinsic literature constant.
--
--   Let $V$ be finite-dimensional, let $\nu$ be log-concave with nonempty support interior, and let $m$ be an additive Haar measure. Let $C\in[0,\infty)$ be represented by a `NNReal`. Suppose every $u$ in the domain of the closed weighted operator satisfies
--   $$\|\operatorname{center}_\nu u\|^2\le C\,\|\overline{\nabla}u\|^2.$$
--   Then
--   $$C_P(\nu)\le C,$$
--   where the right-hand side is interpreted as the coercion of $C$ to $[0,\infty]$.
--
--   This is a general comparison interface between a domain-level energy gap and the intrinsic Poincaré constant. It does not assert the converse in this declaration.
--
--   **Formalization Note.** The conclusion is an inequality in `ENNReal`; the hypothesis is real-valued.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem literatureConstant_le_of_gap (C : NNReal)
--       (hgap : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
--         ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
--           (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2) :
--       Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Selected supporting theorems: [`admissible_iff_memLp_gradient`](https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d), [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc), [`lowerSemicontinuous_sequentialRelaxation`](https://prove2.me/theorems/17428d33-0be2-4fb1-81de-28e6c75ce12e), [`sequentialRelaxation_ofLinearPMap_of_mem`](https://prove2.me/theorems/416527b0-b0d6-435c-8137-3e2f122e7c5a), [`sequentialRelaxation_ofLinearPMap_of_notMem`](https://prove2.me/theorems/e3ef01ee-0dd8-45ce-bd89-f6b6714c8f87).
--
--   Previous: [`norm_center_sq_sub_le`](https://prove2.me/theorems/7596243b-315e-4568-9444-de9ecda59015) · Next: [`literatureConstant_le_inv_of_tendsto`](https://prove2.me/theorems/ad4697ec-e48c-433b-b18f-ec34a0341e53).
--
--   [Source excerpt, lines 345–349](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L345-L349) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L343-L394 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

theorem FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap_readable (C : NNReal)
    (hgap : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) := by sorry
