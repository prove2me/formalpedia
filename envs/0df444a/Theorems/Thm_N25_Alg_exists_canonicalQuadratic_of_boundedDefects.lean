-- Prove2me | Theorems.Thm_N25_Alg_exists_canonicalQuadratic_of_boundedDefects
-- name    : N25.Alg.exists_canonicalQuadratic_of_boundedDefects
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:34.952206+00:00
-- url     : https://prove2.me/theorems/e3209b6a-2452-4e87-89c5-94c71b3b7807
-- title:
--   Canonical quadratic height from bounded defects
-- statement:
--   A nonnegative Northcott function on an abelian group with bounded doubling and parallelogram defects is within a bounded distance of a nonnegative quadratic Northcott function (Tate's limit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib


open Filter Topology

namespace N25.Alg
theorem exists_canonicalQuadratic_of_boundedDefects {G : Type*} [AddCommGroup G] (h₀ : G → ℝ)
    (hnn : ∀ x, 0 ≤ h₀ x) (hN : ∀ B : ℝ, {x | h₀ x ≤ B}.Finite) (C₂ Cp : ℝ)
    (hd : ∀ x, |h₀ (x + x) - 4 * h₀ x| ≤ C₂)
    (hp : ∀ x y, |h₀ (x + y) + h₀ (x - y) - 2 * h₀ x - 2 * h₀ y| ≤ Cp) :
    ∃ q : G → ℝ, (∀ x, 0 ≤ q x) ∧ (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
      (∀ x, |q x - h₀ x| ≤ C₂ / 3) ∧ ∀ B : ℝ, {x | q x ≤ B}.Finite := by sorry
end N25.Alg
