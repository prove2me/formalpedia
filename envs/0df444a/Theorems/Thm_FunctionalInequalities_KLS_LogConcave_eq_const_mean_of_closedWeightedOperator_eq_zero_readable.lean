-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_const_mean_of_closedWeightedOperator_eq_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:17.015909+00:00
-- url     : https://prove2.me/theorems/1a8d321f-1b90-4644-b319-efb67dd1e6ce
-- title:
--   Kernel Of The Closed Weighted Gradient
-- statement:
--   This theorem identifies the kernel of the closed unit-weight gradient with constants.
--
--   Let $V$ be finite-dimensional, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U:V\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-U)$. If
--
--   $$
--   h\in D\!\left(\overline{T}_{\nu,m,I}\right)
--   \quad\text{and}\quad
--   \overline{T}_{\nu,m,I}h=0,
--   $$
--
--   then, as an element of $L^2(\nu)$,
--
--   $$
--   h=\operatorname{const}_{\nu}\!\left(\int_V h\,d\nu\right).
--   $$
--
--   Here `closedWeightedOperator` is the closed unit-weight gradient and `L2.mean` is the $L^2(\nu)$ mean. The conclusion is an operator-kernel characterization, useful in range-density and orthogonality arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eq_const_mean_of_closedWeightedOperator_eq_zero (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U)
--       (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) :
--       (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`ae_add_eq_of_integral_mul_fderiv_eq_zero`](https://prove2.me/theorems/41fc0968-9c28-44e9-bc3c-b52d1929e169), [`exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`](https://prove2.me/theorems/582959f3-9760-49aa-8308-fec3d495a4ec), [`integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/b4c17c79-99e5-4160-b388-7eeda9e935f3), [`restrict_le_smul_of_eq_tilted`](https://prove2.me/theorems/7744a7a5-331d-4220-a88d-91325cd3a0c8).
--
--   Previous: [`integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/b4c17c79-99e5-4160-b388-7eeda9e935f3).
--
--   [Source excerpt, lines 446–451](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L446-L451) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L444-L470 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_readable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) :
    (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by sorry
