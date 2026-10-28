-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_orthogonal_ker_iff_mean_eq_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:09.684285+00:00
-- url     : https://prove2.me/theorems/10368e04-91d8-41a4-9291-f17015f3bc65
-- title:
--   Orthogonality to the Closed-Gradient Kernel Equivalent to Zero Mean
-- statement:
--   This statement identifies the orthogonal complement of the closed unit-gradient kernel with the mean-zero subspace of $L^2$.
--
--   Let $V$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Assume:
--
--   1. $m$ is an additive Haar measure.
--   2. $\nu$ is a log-concave probability measure with nonempty interior of its support.
--   3. $U:V\to\mathbb R$ is $C^2$ and $\nu=m.\operatorname{tilted}(-U)$ (`Measure.tilted`).
--
--   Let $T=$ `KLS.LogConcave.closedWeightedOperator` for $m$ and the identity weight. For every $y\in L^2(\nu)$,
--   $$
--   \left(\forall k\in D(T),\ Tk=0\ \Longrightarrow\ \langle y,k\rangle_{L^2(\nu)}=0\right)
--   \quad\Longleftrightarrow\quad
--   \operatorname{mean}_\nu(y)=0.
--   $$
--   Here the mean is `L2.mean`. This connects the abstract kernel-orthogonality condition to centering in inverse and generator statements.
--
--   **Formalization Note** The vector $y$ is arbitrary in $L^2(\nu)$; it is not required to lie in the form domain $D(T)$. No Poincaré or positive-curvature assumption is present.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem orthogonal_ker_iff_mean_eq_zero
--       (y : Lp ℝ 2 (ν : Measure V)) :
--       (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
--           hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
--             ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) ↔ L2.mean ν y = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Inverse`](https://prove2.me/theorems/fb0b02c9-17f0-4cad-9390-4ccd11bc29f3).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`closedWeightedOperator_eq_zero_iff`](https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37), [`closedWeightedOperator_one_eq_zero`](https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf).
--
--   Next: [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360).
--
--   [Source excerpt, lines 40–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L40-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L37-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse`, declaration `FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable
    (y : Lp ℝ 2 (ν : Measure V)) :
    (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
          ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) ↔ L2.mean ν y = 0 := by sorry
