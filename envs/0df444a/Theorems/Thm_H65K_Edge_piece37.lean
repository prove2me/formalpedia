-- Prove2me | Theorems.Thm_H65K_Edge_piece37
-- name    : H65K.Edge.piece37
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:29:50.291321+00:00
-- url     : https://prove2.me/theorems/dd5e3c7b-5c43-4aab-bdf6-d6a916909544
-- title:
--   Horizontal boundary interval check 37 at height 65000
-- statement:
--   Here $E$ is the generated horizontal boundary data, and $P_{37}$ is the Arda interval checker for piece 37 of its 41-piece partition.
--
--   $$P_{37}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.piece37 :
    H11K.pieceJ E 37 = true := by sorry
