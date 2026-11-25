-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_sq_sub_one_ge
-- name    : GroundTheory.Global.norm_sq_sub_one_ge
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:01.119366+00:00
-- url     : https://prove2.me/theorems/2f5cdc3b-9139-4c62-858f-1d48ef1a791f
-- title:
--   Global: norm sq sub one ge
-- statement:
--   The Global construction uses the norm sq sub one ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L10-L21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter

theorem GroundTheory.Global.norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by sorry
