-- Prove2me | Theorems.Thm_H65K_Edge_piece23
-- name    : H65K.Edge.piece23
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:16:06.749396+00:00
-- url     : https://prove2.me/theorems/17e42ab6-9310-41a0-81bb-a66cc9cf26f1
-- title:
--   Horizontal boundary interval check 23 at height 65000
-- statement:
--   Here $E$ is the generated horizontal boundary data, and $P_{23}$ is the Arda interval checker for piece 23 of its 41-piece partition.
--
--   $$P_{23}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.piece23 :
    H11K.pieceJ E 23 = true := by sorry
