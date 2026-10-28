-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_mul_norm_closedWeightedOperator_toLp_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_toLp_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:19.70198+00:00
-- url     : https://prove2.me/theorems/1216a9e9-dda9-49e5-b0a6-d2e0cf7acb3e
-- title:
--   Smooth Compact-Support Curvature Estimate
-- statement:
--   This is the curvature estimate on smooth compactly supported functions.
--
--   Let $V$, $\nu$, $m$, and $U$ satisfy the heat-model assumptions, with $\nu=m.\operatorname{tilted}(-U)$ and $U\in C^2$. Let $\rho\in\mathbb R$ and assume the Hessian lower bound
--   $$\rho\|v\|^2\le D^2U(x)[v,v]\qquad(x,v\in V).$$
--   For every smooth compactly supported $f$, one has
--   $$\rho\,\|\overline{\nabla}[f]\|^2\le\|A[f]\|^2,$$
--   where $A=\overline{\nabla}^{\,\dagger}\overline{\nabla}$.
--
--   This is the smooth-core form of the curvature inequality and is intended for extension to the whole operator domain.
--
--   **Formalization Note.** The hypothesis does not require $\rho>0$; only the displayed pointwise Hessian inequality is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mul_norm_closedWeightedOperator_toLp_sq_le {ρ : ℝ}
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
--       (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
--       ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--           ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
--         ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
--           ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ hf hfc⟩‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f).
--
--   Supporting theorems: [`mul_integral_gamma_le`](https://prove2.me/theorems/bfd95fe9-63ec-4f27-8573-16f2db598c60), [`norm_toLp_gradient_sq`](https://prove2.me/theorems/08f6268b-f9f3-4fc1-9889-3665ced688d5).
--
--   Previous: [`norm_toLp_gradient_sq`](https://prove2.me/theorems/08f6268b-f9f3-4fc1-9889-3665ced688d5) · Next: [`mul_norm_closedWeightedOperator_sq_le`](https://prove2.me/theorems/df1ab815-889d-4825-b09c-233d7b8156e8).
--
--   [Source excerpt, lines 78–84](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L78-L84) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L75-L114 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_toLp_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_toLp_sq_le_readable {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ hf hfc⟩‖ ^ 2 := by sorry
