-- Prove2me | Theorems.Thm_Freiman_middleRepair_goodness_criterion
-- name    : Freiman.middleRepair_goodness_criterion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:31:29.51695+00:00
-- url     : https://prove2.me/theorems/1f3cc94e-43f7-4dd7-acef-2e772e914d09
-- title:
--   Report incoming-order repair: middleRepair_goodness_criterion
-- statement:
--   Report §2: the other cross inequality and endpoint order are componentwise automatic, so goodness is equivalent to its one potentially separating cross inequality. The forks start in the normalized parent order.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_goodness_criterion :
    ∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2)) := by
  sorry
