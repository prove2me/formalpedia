-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_append_proper
-- name    : Freiman.middleRepair_frame_append_proper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:17.07219+00:00
-- url     : https://prove2.me/theorems/61ec7fee-725d-415e-8980-1b320c0fad80
-- title:
--   middleRepair frame append proper
-- statement:
--   An oriented append extends the two permanent physical prefixes, swapping the two added words when reflected.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_append_proper :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+), middleDigits123 u → middleDigits123 v →
  0 < u.length+v.length → middleProper (middleRepairPhysical s)
    (middleRepairPhysical ⟨⟨s.core.left++u,s.core.right++v⟩,s.reflected⟩) := by
  sorry
