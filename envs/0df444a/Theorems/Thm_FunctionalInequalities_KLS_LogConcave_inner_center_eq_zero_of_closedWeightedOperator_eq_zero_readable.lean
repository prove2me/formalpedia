-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_inner_center_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.inner_center_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:48.487409+00:00
-- url     : https://prove2.me/theorems/60306a5c-e4a6-42ad-8e3e-e1beb0e3909f
-- title:
--   Centered Functions Are Orthogonal To Gradient Kernel Elements
-- statement:
--   This statement identifies the orthogonality of centered data to the kernel of the closed weighted gradient.
--
--   Let $V$, $\nu$, $m$, and $U$ satisfy the heat-model assumptions, with $U\in C^2$. For any $u\in L^2(\nu)$ and any $k$ in the domain of the closed weighted operator, assume
--   $$\overline{\nabla}k=0.$$
--   Then
--   $$\left\langle\operatorname{center}_\nu u,k\right\rangle_{L^2(\nu)}=0.$$
--
--   The result is a technical orthogonality fact used to establish decay of centered heat evolution.
--
--   **Formalization Note.** The kernel characterization used by the declaration identifies such $k$ with a constant $L^2$ class; the conclusion is an equality in the real Hilbert-space inner product.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_center_eq_zero_of_closedWeightedOperator_eq_zero (u : Lp ℝ 2 (ν : Measure V))
--       (k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       (hk : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0) :
--       ⟪L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Supporting theorems: [`closedWeightedOperator_eq_zero_iff`](https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37).
--
--   Previous: [`closedWeightedOperator_eq_zero_iff`](https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37) · Next: [`tendsto_norm_center_apply`](https://prove2.me/theorems/d65ce5f8-31f4-4f05-808f-036c8d89bf33).
--
--   [Source excerpt, lines 540–543](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L540-L543) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L538-L568 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.inner_center_eq_zero_of_closedWeightedOperator_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.inner_center_eq_zero_of_closedWeightedOperator_eq_zero_readable (u : Lp ℝ 2 (ν : Measure V))
    (k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (hk : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0) :
    ⟪L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by sorry
