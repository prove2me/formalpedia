-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_path_choice_normalized
-- name    : Freiman.middleRepair_frame_path_choice_normalized
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:37.802774+00:00
-- url     : https://prove2.me/theorems/209383db-a2d2-48c9-bd9e-1260a4474ae3
-- title:
--   middleRepair frame path choice normalized
-- statement:
--   Countable dependent choice at a normalized starting core: a realized descendant realizes its ancestor, otherwise continue the same target forever.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_path_choice_normalized :
  (∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
  middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d) →
  (∀ (c d : MiddleCore) (t : ℝ), middleRepairProper c d → middleRealized d t → middleRealized c t) →
  ∀ (c : MiddleCore) (t : ℝ), middleNormalized c=c → middleRegular c → middleRepairGood c → t∈middleCover c →
    middleRealized c t ∨ ∃ p : ℕ → MiddleCore, middleRepairPath c t p := by
  sorry
