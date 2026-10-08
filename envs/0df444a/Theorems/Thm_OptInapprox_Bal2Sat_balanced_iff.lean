-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_balanced_iff
-- name    : OptInapprox.Bal2Sat.balanced_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:36.838341+00:00
-- url     : https://prove2.me/theorems/135f9ffd-80fc-4d4d-89cb-6db329be0ea4
-- title:
--   Proof of Thm 4, p. 21 — an instance is balanced iff the linear terms cancel: OBJ = Σ_C w_C(3/4 − yz/4)
-- statement:
--   Let $I$ be a weighted MAX-2SAT instance on $n$ variables (TRUE $= -1$). Then $I$ is balanced in the sense of Definition 12 if and only if the linear terms of the arithmetized objective cancel, that is, if and only if for every assignment $x \in \{-1,1\}^n$
--   $$
--   \mathrm{sat}(x) = \sum_{C = (y \vee z)} w_C\Bigl(\tfrac34 - \tfrac14\, y z\Bigr),
--   $$
--   where each clause is written $(y \vee z)$ with $y = r_ix_i$ and $z = r_jx_j$.
--
--   The forward direction is what makes the objective of a balanced instance a pure quadratic form, which the vector relaxation and the hyperplane rounding then handle exactly as in Goemans–Williamson.
--
--   **Formalization Note** Balancedness is the defined predicate `IsBalanced` (Definition 12, compared as sums over the two halves of the cube); the identity is required for all $2^n$ assignments.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 21, §9, proof of Theorem 4 ("The condition that the instance is balanced is precisely equivalent to the condition that the linear terms cancel out" and the second display OBJ)

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting

namespace OptInapprox.Bal2Sat

/-- Proof of Theorem 4, p. 21: an instance is balanced (Definition 12) iff the linear terms of
the arithmetized objective cancel, i.e. iff for every assignment `x`
`OBJ = Σ_{C=(y∨z)} w_C (3/4 − y·z/4)`. -/
theorem balanced_iff {n : ℕ} (I : Instance n) :
    IsBalanced I ↔ ∀ x : Fin n → Bool,
      satWeight I x = ∑ c, I.w c *
        (3 / 4 - 1 / 4 * (litVal (I.clause c).1 x * litVal (I.clause c).2 x)) := by sorry

end OptInapprox.Bal2Sat
