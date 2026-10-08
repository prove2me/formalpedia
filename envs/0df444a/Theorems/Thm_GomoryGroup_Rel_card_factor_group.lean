-- Prove2me | Theorems.Thm_GomoryGroup_Rel_card_factor_group
-- name    : GomoryGroup.Rel.card_factor_group
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:20.390214+00:00
-- url     : https://prove2.me/theorems/6e8f9a9a-4863-4f63-8aeb-9b38d42e6f53
-- title:
--   p. 262 — the factor module M(I)/M(B) is a finite group with D = |det B| elements
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, let $M(I)=\mathbb Z^m$, and let $M(B)=B\mathbb Z^m$ be the lattice of integer combinations of the columns of $B$. Then the factor module $M(I)/M(B)$ is finite and
--   $$|M(I)/M(B)|=D=|\det B|.$$
--
--   The finiteness of this group is what makes the group problem (4) a finite problem; its order $D$ is the pigeonhole bound of the LEMMA.
--
--   **Formalization Note** $M(B)$ is the range of the $\mathbb Z$-linear map $k\mapsto Bk$ on $\mathbb Z^m$, and the cardinality is `Nat.card` of the quotient module.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 262, second paragraph

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem card_factor_group {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hB : B.det ≠ 0) :
    Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) ∧
      Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by sorry

end GomoryGroup.Rel
