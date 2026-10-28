-- Prove2me | Theorems.Thm_FunctionalInequalities_exists_norm_sq_eq_inner_of_isSymmetric_readable
-- name    : FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:20.764839+00:00
-- url     : https://prove2.me/theorems/9d757bbb-ea20-490b-bd49-9f4d92fbdf19
-- title:
--   Norm Factorization of a Positive Symmetric Quadratic Form
-- statement:
--   This constructs a norm factor for a positive symmetric operator.
--
--   Let $V$ be a finite-dimensional real inner-product space and let $T:V\to V$ be a continuous linear map. Assume:
--
--   1. $T$ is symmetric;
--   2. its quadratic form is nonnegative:
--
--   $$
--   0\le\langle Tv,v\rangle\qquad\text{for every }v\in V.
--   $$
--
--   Then there exists a continuous linear map $B:V\to V$ such that
--
--   $$
--   \langle Tv,v\rangle=\|Bv\|^2
--   \qquad\text{for every }v\in V.
--   $$
--
--   Only existence of $B$ is asserted; it need not be stated symmetric, unique, or positive.
--
--   The result provides the abstract square-root-type factorization used to represent covariance energies by weighted gradients.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_norm_sq_eq_inner_of_isSymmetric (T : V →L[ℝ] V)
--       (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, 0 ≤ inner ℝ (T v) v) :
--       ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (T v) v = ‖B v‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Factorization`](https://prove2.me/theorems/0d70ddf5-b213-40d4-b84d-6c356995c50e).
--
--   [Source excerpt, lines 32–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Factorization.lean#L32-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Factorization.lean#L31-L65 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Factorization`, declaration `FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Factorization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric_readable (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, 0 ≤ inner ℝ (T v) v) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (T v) v = ‖B v‖ ^ 2 := by sorry
