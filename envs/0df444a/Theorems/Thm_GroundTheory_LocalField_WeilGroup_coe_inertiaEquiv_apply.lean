-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_coe_inertiaEquiv_apply
-- name    : GroundTheory.LocalField.WeilGroup.coe_inertiaEquiv_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:38.911799+00:00
-- url     : https://prove2.me/theorems/e53af2c4-21e7-5fd1-9d55-bef0a2002031
-- title:
--   Weil Group: coe inertia Equiv apply
-- statement:
--   The Weil Group construction uses the coe inertia Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L264-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L264-L267

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

theorem GroundTheory.LocalField.WeilGroup.coe_inertiaEquiv_apply (σ : inertia K Ω) :
    ((inertiaEquiv K Ω σ : (maximalUnramifiedExtension K Ω).fixingSubgroup) : Ω ≃ₐ[K] Ω) =
      toGal K Ω σ := by sorry

attribute [defeq] GroundTheory.LocalField.WeilGroup.coe_inertiaEquiv_apply
