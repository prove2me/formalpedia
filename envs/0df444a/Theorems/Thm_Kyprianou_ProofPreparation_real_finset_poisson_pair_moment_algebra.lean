-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_finset_poisson_pair_moment_algebra
-- name    : Kyprianou.ProofPreparation.real_finset_poisson_pair_moment_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:36:14.579261+00:00
-- url     : https://prove2.me/theorems/cd5fc665-c8e2-4d0f-815a-7708f9ecf27e
-- title:
--   Finite Poisson pair-moment kernel collapses to mean-square plus variance
-- statement:
--   For arbitrary finite real weight and intensity functions, the sum over all index pairs of a_i a_j (r_i r_j + δ_ij r_i) equals the square of the weighted intensity sum plus the weighted intensity variance. Pure deterministic finite-sum algebra, used after the diagonal/off-diagonal Poisson count moment kernel to obtain the exact finite simple-function second moment.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite Poisson L² variance algebra.

import Mathlib
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem real_finset_poisson_pair_moment_algebra
    {ι : Type} [DecidableEq ι] (F : Finset ι)
    (a r : ι → ℝ) :
    (∑ i ∈ F, ∑ j ∈ F,
      (a i * a j) * (r i * r j + if i = j then r i else 0)) =
      (∑ i ∈ F, a i * r i) ^ 2 +
      ∑ i ∈ F, a i ^ 2 * r i := by sorry
end Kyprianou.ProofPreparation
