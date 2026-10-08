-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_clause_arith
-- name    : OptInapprox.Bal2Sat.clause_arith
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:10.135+00:00
-- url     : https://prove2.me/theorems/c6898494-594d-4a30-9589-226b79994f24
-- title:
--   Proof of Thm 4, p. 21 — arithmetization: [y ∨ z] = 3/4 − y/4 − z/4 − yz/4 on {−1,1}², so OBJ = Σ_C w_C(3/4 − y/4 − z/4 − yz/4)
-- statement:
--   Treat TRUE as $-1$ and FALSE as $1$. For $y, z \in \{-1, 1\}$, the truth value of the clause $(y \vee z)$ (which is $1$ exactly when $y = -1$ or $z = -1$) is the polynomial
--   $$
--   [\,y \vee z\,] = \tfrac34 - \tfrac14 y - \tfrac14 z - \tfrac14\, y z .
--   $$
--   Consequently, for every weighted MAX-2SAT instance and every assignment $x \in \{-1,1\}^n$, writing each clause as $(y \vee z)$ with $y = r_ix_i$, $z = r_jx_j$,
--   $$
--   \mathrm{sat}(x) = \mathrm{OBJ}(x) = \sum_{C = (y \vee z)} w_C\Bigl(\tfrac34 - \tfrac14 y - \tfrac14 z - \tfrac14\, y z\Bigr).
--   $$
--
--   This turns the combinatorial objective into a quadratic polynomial in the $\pm1$ variables, the starting point of the semidefinite relaxation.
--
--   **Formalization Note** The first conjunct is the pointwise identity on $\{-1,1\}^2$; the second expresses the satisfied weight (defined via Boolean literal truth) through the $\pm1$ literal values `litVal`.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 21, §9, proof of Theorem 4 (arithmetization and the first display OBJ)

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting

namespace OptInapprox.Bal2Sat

/-- Clause arithmetization, proof of Theorem 4, p. 21: with TRUE = −1, a clause `(y ∨ z)` with
`y, z ∈ {−1, 1}` is satisfied (value 1) iff `y = −1` or `z = −1`, and this indicator equals
`3/4 − y/4 − z/4 − yz/4`. Hence the weighted MAX-2SAT objective is
`OBJ = Σ_{C=(y∨z)} w_C (3/4 − y/4 − z/4 − y·z/4)`. -/
theorem clause_arith :
    (∀ y z : ℝ, (y = 1 ∨ y = -1) → (z = 1 ∨ z = -1) →
      (if y = -1 ∨ z = -1 then (1 : ℝ) else 0) = 3 / 4 - 1 / 4 * y - 1 / 4 * z - 1 / 4 * (y * z)) ∧
    ∀ {n : ℕ} (I : Instance n) (x : Fin n → Bool),
      satWeight I x = ∑ c, I.w c *
        (3 / 4 - 1 / 4 * litVal (I.clause c).1 x - 1 / 4 * litVal (I.clause c).2 x
          - 1 / 4 * (litVal (I.clause c).1 x * litVal (I.clause c).2 x)) := by sorry

end OptInapprox.Bal2Sat
