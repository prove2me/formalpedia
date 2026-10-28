-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_lemma_1_scal
-- name    : GeomQM.MomentumMap.lemma_1_scal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:39.585641+00:00
-- url     : https://prove2.me/theorems/ff1d0c5a-a76f-4ce8-8c7e-53a7ca7970bd
-- title:
--   Lemma 1 (scalar product part), p. 4 — ⟨A, B⟩ = ½Tr(AB) is a real, symmetric, positive definite, unitarily invariant scalar product on observables
-- statement:
--   Let $A,B$ be Hermitian $n\times n$ complex matrices and $\langle A,B\rangle=\tfrac12\operatorname{Tr}(AB)$ as in (4). Then:
--
--   1. $\langle A,B\rangle$ is real;
--   2. $\langle A,B\rangle=\langle B,A\rangle$;
--   3. if $A\neq0$ then $\langle A,A\rangle>0$;
--   4. for every unitary $U$,
--   $$\langle UAU^\dagger,\,UBU^\dagger\rangle=\langle A,B\rangle .$$
--
--   This is the "real scalar product that is invariant under the adjoint representation" of Lemma 1. It identifies the observables with $\mathfrak u^*(\mathcal H)$ and is the pairing through which the linear functions $\widehat A$ of Proposition 5 are defined.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 4, Lemma 1, eq. (4)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem lemma_1_scal (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (scal A B).im = 0 ∧
    scal A B = scal B A ∧
    (A ≠ 0 → 0 < (scal A A).re) ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      scal (U * A * star U) (U * B * star U) = scal A B) := by sorry
end GeomQM.MomentumMap
