-- Prove2me | Theorems.Thm_KannanLattice_Core_exists_reduced_basis
-- name    : KannanLattice.Core.exists_reduced_basis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:13:18.545854+00:00
-- url     : https://prove2.me/theorems/4bc1cce6-1665-4676-ac31-907a0aa4a8b3
-- title:
--   Proposition 2.16 (existence form) — every lattice has a reduced basis
-- statement:
--   Let $b_1,\dots,b_m$ be linearly independent vectors of $\mathcal R^k$. Then the lattice $L(b_1,\dots,b_m)$ has a basis $b_1',\dots,b_m'$, i.e. linearly independent vectors with
--
--   $$L(b_1',\dots,b_m')=L(b_1,\dots,b_m),$$
--
--   which is reduced in the sense of Definition 2.6: $b_j'(j)=\Lambda_1(L_j(b'))$ for all $j$ (2.7) and $|b_i'(j)|\le b_j'(j)/2$ for $i>j$ (2.8).
--
--   The proof of Theorem (5.5) starts from exactly this: "Let $b_1,b_2,\dots b_n$ be a reduced basis of the lattice $L=\tau Z^n$".
--
--   **Formalization Note** Proposition 2.16 in the paper says that the basis returned by the procedure SHORTEST satisfies (2.7) and (2.8). The procedure (which calls the LLL algorithm) is not formalized in this mission, so the proposition is stated in the existence form that its correctness implies.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 16, Proposition 2.16 (existence form); p. 11, Definition 2.6

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced

namespace KannanLattice.Core

/-- Proposition 2.16 of Kannan (1987), p. 16, in existence form: every lattice `L(b)` has a basis
that is reduced in the sense of Definition 2.6 ((2.7) and (2.8)). (The paper exhibits the output
of its procedure SHORTEST.) -/
theorem exists_reduced_basis (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ IsReduced b' := by sorry

end KannanLattice.Core
