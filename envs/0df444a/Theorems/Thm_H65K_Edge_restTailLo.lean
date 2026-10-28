-- Prove2me | Theorems.Thm_H65K_Edge_restTailLo
-- name    : H65K.Edge.restTailLo
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:36:20.561077+00:00
-- url     : https://prove2.me/theorems/8cdbb972-6ca1-4580-b7e1-1a4b52a0c3bf
-- title:
--   Horizontal boundary TailLo check at height 65000
-- statement:
--   Here $E$ denotes the generated boundary data and the Boolean predicate $R_{\mathrm{taillo}}$ is the exact checker for the lower final argument bound.
--
--   $$R_{\mathrm{taillo}}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.restTailLo :
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo = true := by sorry
