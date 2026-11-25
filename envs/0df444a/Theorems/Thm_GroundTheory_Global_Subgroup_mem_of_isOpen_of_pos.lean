-- Prove2me | Theorems.Thm_GroundTheory_Global_Subgroup_mem_of_isOpen_of_pos
-- name    : GroundTheory.Global.Subgroup.mem_of_isOpen_of_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:00.811852+00:00
-- url     : https://prove2.me/theorems/e02b3f25-3907-5a07-a830-056157767d65
-- title:
--   Subgroup: mem of is Open of pos
-- statement:
--   The Subgroup construction uses the mem of is Open of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section

theorem GroundTheory.Global.Subgroup.mem_of_isOpen_of_pos (H : Subgroup ℝˣ) (hH : IsOpen (H : Set ℝˣ)) {r : ℝˣ}
    (hr : 0 < (r : ℝ)) : r ∈ H := by sorry
