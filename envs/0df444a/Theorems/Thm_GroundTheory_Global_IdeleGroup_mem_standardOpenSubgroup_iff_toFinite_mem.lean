-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup_iff_toFinite_mem
-- name    : GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup_iff_toFinite_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:30.237375+00:00
-- url     : https://prove2.me/theorems/279ee77d-6389-4f17-93c8-8cdd5262b960
-- title:
--   Idele Group: mem standard Open Subgroup iff to Finite mem
-- statement:
--   The Idele Group construction uses the mem standard Open Subgroup iff to Finite mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L143-L148

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
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
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]

theorem GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup_iff_toFinite_mem (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by sorry
