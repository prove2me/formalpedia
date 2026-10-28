-- Prove2me | Theorems.Thm_H65K_Edge_restHead
-- name    : H65K.Edge.restHead
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:34:02.784009+00:00
-- url     : https://prove2.me/theorems/9efe0eb7-306d-4df5-ae41-9de163f341f2
-- title:
--   Horizontal boundary Head check at height 65000
-- statement:
--   Here $E$ denotes the generated boundary data and the Boolean predicate $R_{\mathrm{head}}$ is the exact checker for partition and endpoint continuity bookkeeping.
--
--   $$R_{\mathrm{head}}(E)=\mathrm{true}$$
--
--   The theorem is a finite rational arithmetic certificate used in the zero-count argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem H65K.Edge.restHead :
    (Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) &&
      eqB (E.x E.m) (ofInt (-1)) &&
      (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
      eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1))) = true := by sorry
