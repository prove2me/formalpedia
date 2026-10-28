-- Prove2me | Theorems.Thm_H65K_Edge_restBox1
-- name    : H65K.Edge.restBox1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:33:28.279987+00:00
-- url     : https://prove2.me/theorems/38bb4bb2-4c23-4b7e-8744-aa39e317a277
-- title:
--   Horizontal boundary Box1 check at height 65000
-- statement:
--   Here $E$ denotes the generated boundary data and the Boolean predicate $R_{\mathrm{box1}}$ is the exact checker for the second boundary endpoint enclosure.
--
--   $$R_{\mathrm{box1}}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.restBox1 :
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1 E.qlo1 E.qhi1 = true := by sorry
