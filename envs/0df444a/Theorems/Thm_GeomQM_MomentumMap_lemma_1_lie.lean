-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_lemma_1_lie
-- name    : GeomQM.MomentumMap.lemma_1_lie
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:40.969066+00:00
-- url     : https://prove2.me/theorems/efeb3afb-6c8a-4441-861b-038a976a3f9d
-- title:
--   Lemma 1 (Lie part), p. 4 — [A, B]₋ = i(AB − BA) makes the Hermitian matrices a Lie algebra isomorphic to u(n) via α(A) = iA
-- statement:
--   Let $A,B,C$ be Hermitian $n\times n$ complex matrices, $\alpha(A)=iA$ as in (2), and $[A,B]_-=\alpha^{-1}(\alpha(A)\alpha(B)-\alpha(B)\alpha(A))=i(AB-BA)$ as in (3). Then:
--
--   1. $[A,B]_-$ is Hermitian;
--   2. $[\cdot,\cdot]_-$ is real-linear in its first argument: $[rA+B,C]_-=r[A,C]_-+[B,C]_-$ for $r\in\mathbb R$;
--   3. it is antisymmetric, $[A,B]_-=-[B,A]_-$;
--   4. it satisfies the Jacobi identity
--   $$[A,[B,C]_-]_-+[B,[C,A]_-]_-+[C,[A,B]_-]_-=0;$$
--   5. $\alpha$ intertwines it with the commutator of $\mathfrak u(\mathcal H)$: $\alpha([A,B]_-)=\alpha(A)\alpha(B)-\alpha(B)\alpha(A)$;
--   6. $\alpha(A)$ is anti-Hermitian;
--   7. every anti-Hermitian matrix $X$ is $\alpha(Y)$ for exactly one Hermitian $Y$.
--
--   Together these say that the observables form a real Lie algebra isomorphic, through $\alpha$, to $\mathfrak u(n)$. This is the Lie half of Lemma 1; the scalar product half is a separate item.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 4, Lemma 1, eqs. (2)–(3)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem lemma_1_lie (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (lieO A B).IsHermitian ∧
    (∀ r : ℝ, lieO (r • A + B) C = r • lieO A C + lieO B C) ∧
    lieO A B = -lieO B A ∧
    lieO A (lieO B C) + lieO B (lieO C A) + lieO C (lieO A B) = 0 ∧
    alpha (lieO A B) = alpha A * alpha B - alpha B * alpha A ∧
    (alpha A)ᴴ = -alpha A ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      ∃! Y : Matrix (Fin n) (Fin n) ℂ, Y.IsHermitian ∧ alpha Y = X) := by sorry
end GeomQM.MomentumMap
