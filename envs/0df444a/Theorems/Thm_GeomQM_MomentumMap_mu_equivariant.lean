-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_mu_equivariant
-- name    : GeomQM.MomentumMap.mu_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:34.165025+00:00
-- url     : https://prove2.me/theorems/220ba797-c563-46fa-a23f-45ff74ee644c
-- title:
--   §3.1.1, p. 11 — the momentum map µ(ψ) = |ψ⟩⟨ψ| takes values in u*(n) and is U(n)-equivariant
-- statement:
--   Let $\mu(\psi)=|\psi\rangle\langle\psi|$ for $\psi\in\mathbb C^n$, and identify $\mathfrak u^*(n)$ with the Hermitian $n\times n$ matrices, on which the coadjoint action of $U(n)$ is $\xi\mapsto U\xi U^\dagger$. Then $\mu(\psi)$ is Hermitian, and for every unitary $U$ and every $\psi$,
--
--   $$\mu(U\psi)=U\,\mu(\psi)\,U^\dagger .$$
--
--   That is, $\mu:\mathbb C^n\cong\mathbb R^{2n}\to\mathfrak u^*(n)$ is equivariant with respect to the defining action of $U(n)$ on $\mathbb C^n$ and the coadjoint action on $\mathfrak u^*(n)$.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 11, §3.1.1 (unnumbered claim)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem mu_equivariant (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (ψ : Fin n → ℂ) :
    (momentumMap ψ).IsHermitian ∧
    momentumMap (U *ᵥ ψ) = U * momentumMap ψ * star U := by sorry
end GeomQM.MomentumMap
