-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_mul_fderiv_eq_neg_integral_mul_inner_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:56.24209+00:00
-- url     : https://prove2.me/theorems/7c322f0f-17ab-4ef7-afc1-582bee9c53ac
-- title:
--   Weak Integration By Parts For The Closed Gradient
-- statement:
--   This theorem is the weak derivative identity for an element of the closed weighted-gradient domain.
--
--   Let $V$ be finite-dimensional, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U:V\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-U)$. Let
--
--   $$
--   h\in D\!\left(\overline{T}_{\nu,m,I}\right),
--   $$
--
--   where $I$ is the identity weight. For every $C^\infty$ compactly supported test function $\phi:V\to\mathbb R$ and every $w\in V$,
--
--   $$
--   \int_V h(x)\,D\phi(x)[w] \,dm(x)
--   =
--   -\int_V \phi(x)\left\langle \overline{T}_{\nu,m,I}h(x),w\right\rangle\,dm(x).
--   $$
--
--   The function $h$ is interpreted through its $L^2(\nu)$ representative, and the closed operator is `closedWeightedOperator`. This provides the weak gradient relation needed for identifying the kernel of the closed operator.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_fderiv_eq_neg_integral_mul_inner (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U)
--       (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {φ : V → ℝ}
--       (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
--       ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m =
--         -∫ x, φ x * ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
--           Lp V 2 (ν : Measure V)) x, w⟫ ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`exists_seq_smooth_tendsto_graph`](https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a), [`tendsto_integral_mul_inner_of_tendsto`](https://prove2.me/theorems/af848101-2a6e-4098-8b0e-6563207a68d5), [`tendsto_integral_mul_of_tendsto`](https://prove2.me/theorems/0ead0018-76f8-4e4a-918c-0de12ef6b171).
--
--   Previous: [`tendsto_integral_mul_inner_of_tendsto`](https://prove2.me/theorems/af848101-2a6e-4098-8b0e-6563207a68d5) · Next: [`integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/b4c17c79-99e5-4160-b388-7eeda9e935f3).
--
--   [Source excerpt, lines 339–346](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L339-L346) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L337-L420 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_readable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m =
      -∫ x, φ x * ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
        Lp V 2 (ν : Measure V)) x, w⟫ ∂m := by sorry
