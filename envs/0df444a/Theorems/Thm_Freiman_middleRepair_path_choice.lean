-- Prove2me | Theorems.Thm_Freiman_middleRepair_path_choice
-- name    : Freiman.middleRepair_path_choice
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:18.964562+00:00
-- url     : https://prove2.me/theorems/d2664e50-420c-4190-b422-26b8ae0c70ef
-- title:
--   middleRepair path choice
-- statement:
--   Normalize the starting core, choose a nonterminal path, and reflect any terminal realization back.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_path_choice :
  (∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
  middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d) →
  (∀ (c d : MiddleCore) (t : ℝ), middleRepairProper c d → middleRealized d t → middleRealized c t) →
  ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
    middleRealized c t ∨ ∃ p : ℕ → MiddleCore, middleRepairPath c t p := by
  sorry
