-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_theorem_3
-- name    : HollandsSanders.CFTBound.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:09.523355+00:00
-- url     : https://prove2.me/theorems/83840854-898a-4302-b45b-072e920ff31d
-- title:
--   Theorem 3, p. 46 — E_R(ω) ⩽ E_N(ω)
-- statement:
--   Let $\mathfrak A_A,\mathfrak A_B$ be commuting von Neumann algebras on a Hilbert space $\mathcal H$ and let $\omega$ be a normal state on their join $\mathfrak A_A\vee\mathfrak A_B$. Then the relative entanglement entropy is bounded by the logarithmic dominance:
--   $$E_R(\omega)\leqslant E_N(\omega).$$
--
--   The inequality turns any separable functional dominating $\omega$ into an upper bound on $E_R(\omega)$; it is the first link of the chain $E_R\le E_N\le E_M$ used to bound the vacuum entanglement of a conformal field theory.
--
--   **Formalization Note.** $E_R$ and $E_N$ are the `EReal`-valued infima of the definition file, $+\infty$ on empty sets; the relative entropy is Araki's in Kosaki's variational form.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 46, Theorem 3

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Theorem 3 (p. 46): `E_R(ω) ⩽ E_N(ω)` for a normal state `ω` on `𝔄_A ∨ 𝔄_B`. -/
theorem theorem_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {AA AB : VonNeumannAlgebra H} (hcomm : AA ≤ AB.commutant)
    (ω : (H →L[ℂ] H) → ℂ) (hω : IsNormalState (join AA AB : Set (H →L[ℂ] H)) ω) :
    ER AA AB ω ≤ EN AA AB ω := by sorry

end HollandsSanders.CFTBound
