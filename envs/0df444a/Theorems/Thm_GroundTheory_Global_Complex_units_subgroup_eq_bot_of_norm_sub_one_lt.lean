-- Prove2me | Theorems.Thm_GroundTheory_Global_Complex_units_subgroup_eq_bot_of_norm_sub_one_lt
-- name    : GroundTheory.Global.Complex.units_subgroup_eq_bot_of_norm_sub_one_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:40.444573+00:00
-- url     : https://prove2.me/theorems/aed8f8b8-1f23-442e-9e54-a156984dde4a
-- title:
--   Complex: units subgroup eq bot of norm sub one lt
-- statement:
--   The Complex construction uses the units subgroup eq bot of norm sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L75-L84

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
open GroundTheory.Global.Complex

theorem GroundTheory.Global.Complex.units_subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by sorry
