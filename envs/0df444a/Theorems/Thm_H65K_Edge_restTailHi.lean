-- Prove2me | Theorems.Thm_H65K_Edge_restTailHi
-- name    : H65K.Edge.restTailHi
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:35:37.308182+00:00
-- url     : https://prove2.me/theorems/296a6417-040c-446b-93cf-138ac0cea236
-- title:
--   Horizontal boundary TailHi check at height 65000
-- statement:
--   Here $E$ denotes the generated boundary data and the Boolean predicate $R_{\mathrm{tailhi}}$ is the exact checker for the upper final argument bound.
--
--   $$R_{\mathrm{tailhi}}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.restTailHi :
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi = true := by sorry
