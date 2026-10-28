-- Prove2me | Theorems.Thm_H65K_Edge_hAH
-- name    : H65K.Edge.hAH
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:42:27.183298+00:00
-- url     : https://prove2.me/theorems/acb57f77-1720-4813-9146-99f91140b2d1
-- title:
--   Horizontal zeta argument enclosure at height 65000
-- statement:
--   Let $E$ be the recorded horizontal-boundary certificate, with rational endpoints $E_{m lo},E_{m hi}$. The change in the argument of the Riemann zeta function along the horizontal segment from $2+65000i$ to $-1+65000i$ satisfies
--
--   $$\Delta_{[2,-1]+65000i}\arg\zeta\in[E_{\rm lo},E_{\rm hi}].$$
--
--   The interval follows from the finite edge checks and their analytic soundness.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_Turing.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem H65K.Edge.hAH :
    DiffractionCore.argChangeHoriz riemannZeta (65000 : ℝ) 2 (-1) ∈
      Set.Icc H65K.Edge.E.Lo.val H65K.Edge.E.Hi.val := by sorry
