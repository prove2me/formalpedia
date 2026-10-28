-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_proposition_1
-- name    : GeomQM.MomentumMap.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:43.107557+00:00
-- url     : https://prove2.me/theorems/9ce1822d-4661-475d-a2ca-d8218813b973
-- title:
--   Proposition 1, p. 5 — ½Tr(AB) is invariant for both products, and ad₋ is a derivation of the Jordan product
-- statement:
--   Let $A,B,C$ be Hermitian $n\times n$ complex matrices, with $[A,B]_-=i(AB-BA)$, $[A,B]_+=A\circ B=\tfrac12(AB+BA)$ and $\langle A,B\rangle=\tfrac12\operatorname{Tr}(AB)$. Then (7):
--
--   $$\langle[A,B]_-,C\rangle=\langle A,[B,C]_-\rangle,\qquad \langle[A,B]_+,C\rangle=\langle A,[B,C]_+\rangle,$$
--
--   and the compatibility relation (8) holds:
--
--   $$[A,B\circ C]_-=[A,B]_-\circ C+B\circ[A,C]_- ,$$
--
--   that is, $\mathrm{ad}_-$ is a derivation of the Jordan algebra. Relation (8) is one of the two axioms that make the observables a Jordan–Lie algebra (Lemma 3).
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 5, Proposition 1, eqs. (7)–(8)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem proposition_1 (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    scal (lieO A B) C = scal A (lieO B C) ∧
    scal (jordan A B) C = scal A (jordan B C) ∧
    lieO A (jordan B C) = jordan (lieO A B) C + jordan B (lieO A C) := by sorry
end GeomQM.MomentumMap
