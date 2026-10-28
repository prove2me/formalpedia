-- Prove2me | Theorems.Thm_H65K_Edge_piece03
-- name    : H65K.Edge.piece03
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:18:41.099152+00:00
-- url     : https://prove2.me/theorems/979fbbf5-48e0-4c95-a693-a2d4da5053d5
-- title:
--   Horizontal boundary interval check 3 at height 65000
-- statement:
--   Here $E$ is the generated horizontal boundary data, and $P_{3}$ is the Arda interval checker for piece 3 of its 41-piece partition.
--
--   $$P_{3}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.piece03 :
    H11K.pieceJ E 3 = true := by sorry
