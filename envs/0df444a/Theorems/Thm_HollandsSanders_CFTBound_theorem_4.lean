-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_theorem_4
-- name    : HollandsSanders.CFTBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:18.542196+00:00
-- url     : https://prove2.me/theorems/fc5afd83-8392-415c-a055-3c9dc1038149
-- title:
--   Theorem 4, p. 47 — E_N(ω) ⩽ E_M(ω)
-- statement:
--   Let $\mathfrak A_A,\mathfrak A_B$ be commuting, statistically independent von Neumann algebras on $\mathcal H$, and let $\Omega$ be a unit vector that is cyclic and separating for $\mathfrak A_A'$ and $\mathfrak A_B'$, with vector state $\omega$. Then the logarithmic dominance is bounded by the modular entanglement measure:
--   $$E_N(\omega)\leqslant E_M(\omega)=\ln\min\big(\|\Psi^A\|_1,\|\Psi^B\|_1\big).$$
--
--   Combined with Theorem 3 it gives $E_R(\omega)\le\ln\|\Psi^A\|_1$, which is how nuclearity of a modular map bounds the relative entanglement entropy.
--
--   **Formalization Note.** $\Psi^A$ uses the modular operator of $\mathfrak A_B'$ and $\Psi^B$ that of $\mathfrak A_A'$, both at $\Omega$; the hypotheses pin these modular data to the right algebras and vector.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 47, Theorem 4, under the standing assumptions of §3 (p. 35) and §3.6 (p. 46, footnote 28)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Theorem 4 (p. 47): `E_N(ω) ⩽ E_M(ω)` for the vector state `ω` of `Ω`, under the standing
assumption of §3.6 (`Ω` cyclic and separating for `𝔄′_A`, `𝔄′_B`: modular data `SA`, `SB`) and
the standing assumptions of §3 (commuting, statistically independent `𝔄_A`, `𝔄_B`). -/
theorem theorem_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {AA AB : VonNeumannAlgebra H} (hcomm : AA ≤ AB.commutant) (hind : IsStatIndependent AA AB)
    (Om : H) (SA SB : StandardModularData H)
    (hSA : SA.M = AA.commutant) (hSB : SB.M = AB.commutant) (hxA : SA.xi = Om) (hxB : SB.xi = Om) :
    EN AA AB (vecState Om) ≤ EM AA AB SA SB := by sorry

end HollandsSanders.CFTBound
