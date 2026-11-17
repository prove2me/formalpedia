-- Prove2me | Theorems.Thm_N25_Alg_exists_invariant_quadratic_of_pow_five
-- name    : N25.Alg.exists_invariant_quadratic_of_pow_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:34.454197+00:00
-- url     : https://prove2.me/theorems/5ccc1bc9-1db5-401d-97c0-23c7e828c50f
-- title:
--   Averaging a quadratic height over an automorphism of order dividing five
-- statement:
--   Averaging a nonnegative quadratic Northcott function over an additive automorphism g with g^5 = 1 gives a g-invariant one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib

namespace N25.Alg
theorem exists_invariant_quadratic_of_pow_five {G : Type*} [AddCommGroup G] (g : G →+ G)
    (hg : ∀ x, g (g (g (g (g x)))) = x) (q₀ : G → ℝ) (hnn : ∀ x, 0 ≤ q₀ x)
    (hpar : ∀ x y, q₀ (x + y) + q₀ (x - y) = 2 * q₀ x + 2 * q₀ y)
    (hN : ∀ B : ℝ, {x | q₀ x ≤ B}.Finite) :
    ∃ q : G → ℝ, (∀ x, 0 ≤ q x) ∧ (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
      (∀ x, q (g x) = q x) ∧ ∀ B : ℝ, {x | q x ≤ B}.Finite := by sorry
end N25.Alg
