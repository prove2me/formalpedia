-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_lemma_3
-- name    : GeomQM.MomentumMap.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:38.316987+00:00
-- url     : https://prove2.me/theorems/e04573a5-9fa4-4a00-9681-5a6abb42373a
-- title:
--   Lemma 3, p. 5 — the observables form a Jordan–Lie algebra (Definition 2): Lie and Jordan axioms, (8), and the associator identity (9) with ℏ = 1
-- statement:
--   Let $A,B,C$ be Hermitian $n\times n$ complex matrices, with $[A,B]_-=i(AB-BA)$ and $A\circ B=\tfrac12(AB+BA)$. Then $(\mathcal O,[\cdot,\cdot]_-,\circ)$ is a Jordan–Lie algebra in the sense of Definition 2: $[A,B]_-$ is again Hermitian, real-linear in the first slot, antisymmetric, and satisfies the Jacobi identity; $A\circ B$ is again Hermitian, real-linear in the first slot, commutative, and satisfies the Jordan identity $(A\circ B)\circ(A\circ A)=A\circ(B\circ(A\circ A))$ of Definition 1; and the two further axioms of Definition 2 hold: the compatibility relation (8),
--
--   $$[A,B\circ C]_-=[A,B]_-\circ C+B\circ[A,C]_-,$$
--
--   and the associator identity (9) with $\hbar=1$:
--
--   $$(A\circ B)\circ C-A\circ(B\circ C)=\tfrac14\,[[A,C]_-,B]_- .$$
--
--   The Lie and Jordan clauses repeat Lemmas 1 and 2, so that the statement is the whole of Definition 2 and not only its two extra axioms.
--
--   **Formalization Note** Definition 2 asks for (9) "for some $\hbar\in\mathbb R$"; the statement fixes the value $\hbar=1$ produced by the normalisations (3) and (6), which is stronger than the existential form.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 5, Definition 2 and Lemma 3, eqs. (8)–(9)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem lemma_3 (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (lieO A B).IsHermitian ∧
    (∀ r : ℝ, lieO (r • A + B) C = r • lieO A C + lieO B C) ∧
    lieO A B = -lieO B A ∧
    lieO A (lieO B C) + lieO B (lieO C A) + lieO C (lieO A B) = 0 ∧
    (jordan A B).IsHermitian ∧
    (∀ r : ℝ, jordan (r • A + B) C = r • jordan A C + jordan B C) ∧
    jordan A B = jordan B A ∧
    jordan (jordan A B) (jordan A A) = jordan A (jordan B (jordan A A)) ∧
    lieO A (jordan B C) = jordan (lieO A B) C + jordan B (lieO A C) ∧
    jordan (jordan A B) C - jordan A (jordan B C) =
      (1 / 4 : ℝ) • lieO (lieO A C) B := by sorry
end GeomQM.MomentumMap
