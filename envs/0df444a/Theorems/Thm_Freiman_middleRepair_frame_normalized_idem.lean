-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_normalized_idem
-- name    : Freiman.middleRepair_frame_normalized_idem
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:48.935127+00:00
-- url     : https://prove2.me/theorems/480c3059-5f7c-4d1b-b72e-f794df087dfe
-- title:
--   middleRepair frame normalized idem
-- statement:
--   A second width normalization preserves the current order, including a tie.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_normalized_idem :
  ∀ c : MiddleCore, middleNormalized (middleNormalized c) = middleNormalized c := by
  sorry
