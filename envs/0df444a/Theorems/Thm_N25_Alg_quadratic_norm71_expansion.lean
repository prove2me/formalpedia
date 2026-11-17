-- Prove2me | Theorems.Thm_N25_Alg_quadratic_norm71_expansion
-- name    : N25.Alg.quadratic_norm71_expansion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:34.30776+00:00
-- url     : https://prove2.me/theorems/54df38af-368c-4007-8f81-d9ca708bf9e1
-- title:
--   Expansion of an invariant quadratic form under a norm-71 element
-- statement:
--   If d satisfies 1 + d + d^2 + d^3 + d^4 = 0 and q is a nonnegative d-invariant quadratic function, then q((2 + 4d + d^2) x) >= (7/3) q(x).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib

namespace N25.Alg
theorem quadratic_norm71_expansion {G : Type*} [AddCommGroup G] (d : G →+ G)
    (hΦ : ∀ x, x + d x + d (d x) + d (d (d x)) + d (d (d (d x))) = 0)
    (q : G → ℝ) (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hinv : ∀ x, q (d x) = q x) (hnn : ∀ x, 0 ≤ q x) (x : G) :
    (7 / 3 : ℝ) * q x ≤ q (2 • x + 4 • d x + d (d x)) := by sorry
end N25.Alg
