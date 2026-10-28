-- Prove2me | Theorems.Thm_H65K_Edge_piece21
-- name    : H65K.Edge.piece21
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:31.69269+00:00
-- url     : https://prove2.me/theorems/1f0dbd3e-0d79-411c-ac7f-98e5bfc5b855
-- title:
--   Horizontal boundary interval check 21 at height 65000
-- statement:
--   Here $E$ is the generated horizontal boundary data, and $P_{21}$ is the Arda interval checker for piece 21 of its 41-piece partition.
--
--   $$P_{21}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.piece21 :
    H11K.pieceJ E 21 = true := by sorry
