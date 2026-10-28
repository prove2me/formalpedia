-- Prove2me | Theorems.Thm_H65K_Count121_chk
-- name    : H65K.Count121.chk
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:20:40.917995+00:00
-- url     : https://prove2.me/theorems/6d9f181c-c972-400b-bfb0-b24953589fa7
-- title:
--   Arithmetic count budget for the 121-to-65000 band
-- statement:
--   Let $E,G_0,G_1$ be the recorded rational argument-change and gamma enclosures. The finite band and side checks for the count $K=85250$ both hold:
--
--   $$\operatorname{validBS}(121,65000,65121/2,4209284657/4,K,E)=\mathrm{true},\qquad\operatorname{k6sideB}(G_0,G_1,E)=\mathrm{true}.$$
--
--   This is the arithmetic budget used by the separate argument-principle proof.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_Turing.lean

import Definitions.Def_ArdaRH65K_Count121Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem H65K.Count121.chk :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 65000) (Q.frac 65121 2)
      (Q.frac 4209284657 4) 85250 H65K.Count121.E &&
      k6sideB H65K.Count121.G0 H65K.Count121.G1 H65K.Count121.E) = true := by sorry
