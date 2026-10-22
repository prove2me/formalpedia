-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_eq_219
-- name    : HollandsSanders.CFTBound.eq_219
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:18.746651+00:00
-- url     : https://prove2.me/theorems/c3562148-da8b-47b8-bc2a-6747f8c54379
-- title:
--   Eq. (219), p. 81 — Δ_A = e^{−i(ln r)D} Δ_{B′} e^{i(ln r)D}
-- statement:
--   In a conformal field theory in $d+1$ dimensions, $d\ge2$, let $0<r<1$, let $\Delta_A$ be the modular operator of the algebra of the double cone over the ball of radius $r$, and $\Delta_{B'}$ that of the double cone over the unit ball, both with the vacuum vector. Then
--   $$\Delta_A=e^{-i(\ln r)D}\,\Delta_{B'}\,e^{i(\ln r)D},$$
--   stated for the modular groups: $\Delta_A^{it}=e^{-i(\ln r)D}\Delta_{B'}^{it}e^{i(\ln r)D}$ for all $t\in\mathbb R$.
--
--   The region $A$ is obtained from $B'$ by the dilation $x\mapsto rx$, and the modular data follow the geometry. Together with Lemma 13 this gives the operator identity (212).
--
--   **Formalization Note.** Two self-adjoint positive operators with the same unitary groups $\Delta^{it}$ coincide, so the statement on modular groups is equivalent to (219).
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 81, eq. (219)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_HollandsSanders_CFTBound_Conformal
open OAI.BoundedRecovery Real
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- (219), p. 81: for `0 < r < 1`, with `A` the double cone of radius `r` and `B′` the unit double
cone, `Δ_A = e^{−i(ln r)D} Δ_{B′} e^{i(ln r)D}`, stated for the modular groups:
`Δ_A^{it} = e^{−i(ln r)D} Δ_{B′}^{it} e^{i(ln r)D}` for all `t`. -/
theorem eq_219 {d : ℕ} (hd : 2 ≤ d) {H0 : Type*} [NormedAddCommGroup H0]
    [InnerProductSpace ℂ H0] [CompleteSpace H0] (T : CFTVacuum d H0)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (SA SB : StandardModularData H0)
    (hSA : SA.M = T.net (ballDiamond r)) (hxA : SA.xi = T.vac)
    (hSB : SB.M = T.net (ballDiamond 1)) (hxB : SB.xi = T.vac) (t : ℝ) :
    SA.D.unitary t = T.Dil.unitary (-Real.log r) * SB.D.unitary t * T.Dil.unitary (Real.log r) := by sorry

end HollandsSanders.CFTBound
