-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_card_factorGroup
-- name    : Gomory69.Asymptotic.card_factorGroup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:02:47.513979+00:00
-- url     : https://prove2.me/theorems/1fd0d93f-9260-4507-9da2-6d2819dfff3b
-- title:
--   p. 459 — the group M(I)/M(B) is finite of order |det B|
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $M(B)$ the lattice of integer combinations of its columns and $\mathcal G=M(I)/M(B)$ with $M(I)=\mathbb Z^m$. Then $\mathcal G$ is finite and
--
--   $$|\mathcal G|=|\det B|.$$
--
--   This lets $|\mathcal G|$ be replaced by $D=|\det B|$ in THEOREM 1, which is how $D$ enters THEOREM 4.
--
--   **Formalization Note** The conclusion states finiteness explicitly, since `Nat.card` of an infinite type is $0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 459 (after the proof of THEOREM 1)

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- p. 459: for a nonsingular integer `m × m` matrix `B`, the factor group
`𝒢 = M(I)/M(B)` is finite and `|𝒢| = |det B|`. -/
theorem card_factorGroup {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by sorry

end Gomory69.Asymptotic
