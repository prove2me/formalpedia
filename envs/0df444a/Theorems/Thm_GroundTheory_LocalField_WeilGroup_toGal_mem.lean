-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_toGal_mem
-- name    : GroundTheory.LocalField.WeilGroup.toGal_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:14:40.378798+00:00
-- url     : https://prove2.me/theorems/1565836d-2ed5-4ecf-af56-9f34ac353e57
-- title:
--   Weil Group: to Gal mem
-- statement:
--   The Weil Group construction uses the to Gal mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L127-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L127-L127

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
open GroundTheory.LocalField.WeilGroup
variable {K Ω}

theorem GroundTheory.LocalField.WeilGroup.toGal_mem (σ : WeilGroup K Ω) : toGal K Ω σ ∈ weilSubgroup K Ω := by sorry
