-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_psi_le_phi
-- name    : HollandsSanders.CFTBound.psi_le_phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:40.358359+00:00
-- url     : https://prove2.me/theorems/276205ef-6139-47ce-a39e-7a747bfb91f4
-- title:
--   p. 56 (and p. 79) — ‖Ψ^A‖₁ ⩽ ‖Φ^A‖₁ for 𝔄_A ⊆ 𝔄_{B′} ⊆ 𝔄′_B
-- statement:
--   Let $\mathfrak A_A\subseteq\mathfrak N\subseteq\mathfrak A_B'$ be von Neumann algebras on $\mathcal H$ and let $\Omega$ be a vector that is cyclic and separating for $\mathfrak N$ and for $\mathfrak A_B'$, with modular operators $\Delta_{\mathfrak N}$ and $\Delta_{\mathfrak A_B'}$. Define on $\mathfrak A_A$
--   $$\Psi^A(a)=\Delta_{\mathfrak A_B'}^{1/4}a\Omega,\qquad\Phi^A(a)=\Delta_{\mathfrak N}^{1/4}a\Omega.$$
--   Then
--   $$\|\Psi^A\|_1\leqslant\|\Phi^A\|_1.$$
--
--   In the paper $\mathfrak N=\mathfrak A_{B'}$ is the algebra of the complement of $B$; the inequality lets the modular nuclearity of $\Phi^A$ bound $E_M$, and hence $E_R$.
--
--   **Formalization Note.** Nuclear norms are in $[0,\infty]$, so the statement includes the case where $\Phi^A$ is not nuclear.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 56 (after a5′)), and p. 79 (proof of Theorem 13)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- p. 56 (also proof of Theorem 13, p. 79): if `𝔄_A ⊆ N ⊆ 𝔄′_B` and `Ω` is cyclic and separating
for `N` and `𝔄′_B`, then `‖Ψ^A‖₁ ⩽ ‖Φ^A‖₁`, where `Ψ^A(a) = Δ_{𝔄′_B}^{1/4} a Ω` and
`Φ^A(a) = Δ_N^{1/4} a Ω` on `𝔄_A`. -/
theorem psi_le_phi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {AA AB N : VonNeumannAlgebra H} (hAN : AA ≤ N) (hNB : N ≤ AB.commutant)
    (SB SN : StandardModularData H) (hSB : SB.M = AB.commutant) (hSN : SN.M = N)
    (hx : SB.xi = SN.xi) :
    nuclearNorm1 (AA : Set (H →L[ℂ] H)) (quarterMap SB) ≤
      nuclearNorm1 (AA : Set (H →L[ℂ] H)) (quarterMap SN) := by sorry

end HollandsSanders.CFTBound
