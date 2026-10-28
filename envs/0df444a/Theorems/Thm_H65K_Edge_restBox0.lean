-- Prove2me | Theorems.Thm_H65K_Edge_restBox0
-- name    : H65K.Edge.restBox0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:32:50.070643+00:00
-- url     : https://prove2.me/theorems/f7c8f4d1-0499-414c-a594-bb4fd1473f96
-- title:
--   Horizontal boundary Box0 check at height 65000
-- statement:
--   Here $E$ denotes the generated boundary data and the Boolean predicate $R_{\mathrm{box0}}$ is the exact checker for the first boundary endpoint enclosure.
--
--   $$R_{\mathrm{box0}}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.restBox0 :
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 = true := by sorry
