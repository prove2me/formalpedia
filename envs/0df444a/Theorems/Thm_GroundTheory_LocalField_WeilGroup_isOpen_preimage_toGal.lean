-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_isOpen_preimage_toGal
-- name    : GroundTheory.LocalField.WeilGroup.isOpen_preimage_toGal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:14.153945+00:00
-- url     : https://prove2.me/theorems/68365d58-baee-5dae-81e6-a569727caaeb
-- title:
--   Weil Group: is Open preimage to Gal
-- statement:
--   The Weil Group construction uses the is Open preimage to Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L286-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L286-L288

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

theorem GroundTheory.LocalField.WeilGroup.isOpen_preimage_toGal {U : Set (Ω ≃ₐ[K] Ω)} (hU : IsOpen U) :
    IsOpen (toGal K Ω ⁻¹' U) := by sorry
