-- Prove2me | Theorems.Thm_GroundTheory_Global_Complex_units_noSmallSubgroups
-- name    : GroundTheory.Global.Complex.units_noSmallSubgroups
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:20.926253+00:00
-- url     : https://prove2.me/theorems/feff3089-69c5-4454-8c36-b47a50f3b00c
-- title:
--   Complex: units no Small Subgroups
-- statement:
--   The Complex construction uses the units no Small Subgroups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L86-L91

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

theorem GroundTheory.Global.Complex.units_noSmallSubgroups : NoSmallSubgroups ℂˣ := by sorry
