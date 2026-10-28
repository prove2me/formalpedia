-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_eq_zero_iff_readable
-- name    : FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:11.749316+00:00
-- url     : https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37
-- title:
--   Kernel Characterization for the Closed Unit Gradient
-- statement:
--   This statement characterizes the kernel of the closed unit gradient in the smooth tilted-measure setting.
--
--   Let $V$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Assume:
--
--   1. $m$ is an additive Haar measure on $V$.
--   2. $\nu$ is a log-concave probability measure with $\operatorname{int}(\operatorname{supp}\nu)\ne\varnothing$.
--   3. $U:V\to\mathbb R$ is $C^2$ and $\nu=m.\operatorname{tilted}(-U)$, using `Measure.tilted`.
--
--   Let $T=$ `KLS.LogConcave.closedWeightedOperator` for the identity weight and $m$. For every $h\in D(T)$,
--   $$
--   Th=0\quad\Longleftrightarrow\quad h=\operatorname{mean}_\nu(h)\mathbf1.
--   $$
--   The mean and constant vector are `L2.mean` and `L2.const`. This identifies precisely the constant vectors in the gradient kernel and supports centered operator formulations.
--
--   **Formalization Note** The equality on the right is in $L^2(\nu)$, equivalently equality of representatives almost everywhere. No strict curvature lower bound or Poincaré bound is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedWeightedOperator_eq_zero_iff
--       (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
--       hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0 ↔
--         (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`closedWeightedOperator_one_eq_zero`](https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf), [`eq_const_mean_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/1a8d321f-1b90-4644-b319-efb67dd1e6ce).
--
--   Previous: [`literatureConstant_le_inv_of_tendsto`](https://prove2.me/theorems/ad4697ec-e48c-433b-b18f-ec34a0341e53) · Next: [`inner_center_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/60306a5c-e4a6-42ad-8e3e-e1beb0e3909f).
--
--   [Source excerpt, lines 499–502](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L499-L502) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L496-L536 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff_readable
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0 ↔
      (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by sorry
