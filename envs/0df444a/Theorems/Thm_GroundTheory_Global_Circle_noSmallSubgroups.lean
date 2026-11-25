-- Prove2me | Theorems.Thm_GroundTheory_Global_Circle_noSmallSubgroups
-- name    : GroundTheory.Global.Circle.noSmallSubgroups
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:49.573916+00:00
-- url     : https://prove2.me/theorems/9dd9d59f-2720-4fb5-a8a0-65d265d91565
-- title:
--   Circle: no Small Subgroups
-- statement:
--   The Circle construction uses the no Small Subgroups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L64-L69

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

theorem GroundTheory.Global.Circle.noSmallSubgroups : NoSmallSubgroups Circle := by sorry
