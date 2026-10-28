-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:08.765982+00:00
-- url     : https://prove2.me/theorems/b4c17c79-99e5-4160-b388-7eeda9e935f3
-- title:
--   Zero Closed Gradient Implies Zero Weak Derivative Pairings
-- statement:
--   This theorem states the vanishing weak-gradient consequence of a zero closed weighted gradient.
--
--   Let $V$, $m$, $\nu$, and $U$ satisfy the finite-dimensional, Haar, log-concavity, nonempty-support-interior, and tilted-law assumptions above. Let $h\in D(\overline{T}_{\nu,m,I})$ satisfy
--
--   $$
--   \overline{T}_{\nu,m,I}h=0.
--   $$
--
--   Then for every smooth compactly supported $\phi:V\to\mathbb R$ and every $w\in V$,
--
--   $$
--   \int_V h(x)\,D\phi(x)[w] \,dm(x)=0.
--   $$
--
--   This is an auxiliary kernel lemma: it converts the operator equation into vanishing distributional derivatives with respect to Haar measure. It does not itself identify $h$ as a constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U)
--       (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) {φ : V → ℝ}
--       (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
--       ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70), [`integral_mul_fderiv_eq_neg_integral_mul_inner`](https://prove2.me/theorems/7c322f0f-17ab-4ef7-afc1-582bee9c53ac).
--
--   Previous: [`integral_mul_fderiv_eq_neg_integral_mul_inner`](https://prove2.me/theorems/7c322f0f-17ab-4ef7-afc1-582bee9c53ac) · Next: [`eq_const_mean_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/1a8d321f-1b90-4644-b319-efb67dd1e6ce).
--
--   [Source excerpt, lines 424–430](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L424-L430) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L422-L442 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m = 0 := by sorry
