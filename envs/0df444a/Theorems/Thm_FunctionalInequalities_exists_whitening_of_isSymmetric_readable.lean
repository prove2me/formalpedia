-- Prove2me | Theorems.Thm_FunctionalInequalities_exists_whitening_of_isSymmetric_readable
-- name    : FunctionalInequalities.exists_whitening_of_isSymmetric_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:34.664319+00:00
-- url     : https://prove2.me/theorems/2412bf64-6088-4a49-aeb3-8a6655511722
-- title:
--   Whitening Equivalence for Positive Definite Symmetric Operators
-- statement:
--   This is a finite-dimensional whitening existence theorem.
--
--   Let $V$ be a finite-dimensional real inner-product normed space and let $T:V\to V$ be continuous linear. Assume:
--
--   1. $T$ is symmetric;
--   2. $\langle Tv,v\rangle>0$ for every nonzero $v\in V$.
--
--   Then there exists a continuous linear equivalence $W:V\simeq V$ such that $W$ is self-adjoint and
--
--   $$\langle T(Wu),Wv\rangle=\langle u,v\rangle\qquad\text{for all }u,v\in V.$$
--
--   Only existence of a self-adjoint whitening equivalence is asserted; positivity or uniqueness of $W$ is not part of the conclusion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_whitening_of_isSymmetric (T : V →L[ℝ] V)
--       (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v) :
--       ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
--         ∀ u v, inner ℝ (T (W u)) (W v) = inner ℝ u v
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Whitening`](https://prove2.me/theorems/47b0b944-6abf-4f6e-a39a-7b55e36f44ae).
--
--   [Source excerpt, lines 44–47](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Whitening.lean#L44-L47) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Whitening.lean#L42-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Whitening`, declaration `FunctionalInequalities.exists_whitening_of_isSymmetric`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Whitening

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.exists_whitening_of_isSymmetric_readable (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (T (W u)) (W v) = inner ℝ u v := by sorry
