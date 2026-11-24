-- Prove2me | Theorems.Thm_GroundTheory_Global_Circle_subgroup_eq_bot_of_norm_sub_one_lt
-- name    : GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:26.774812+00:00
-- url     : https://prove2.me/theorems/f7390108-9dce-4ad0-8f63-720f55389958
-- title:
--   Circle: subgroup eq bot of norm sub one lt
-- statement:
--   The Circle construction uses the subgroup eq bot of norm sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L53-L62

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
open GroundTheory.Global.Circle

theorem GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup Circle)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by sorry
