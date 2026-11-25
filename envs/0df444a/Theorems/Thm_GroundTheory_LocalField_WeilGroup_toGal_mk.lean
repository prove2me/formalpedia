-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_toGal_mk
-- name    : GroundTheory.LocalField.WeilGroup.toGal_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:13.048791+00:00
-- url     : https://prove2.me/theorems/919da89b-b99c-4646-bcd6-6c00cbaea5cc
-- title:
--   Weil Group: to Gal mk
-- statement:
--   The Weil Group construction uses the to Gal mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L135-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L135-L135

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

theorem GroundTheory.LocalField.WeilGroup.toGal_mk (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ weilSubgroup K Ω) : toGal K Ω (mk σ hσ) = σ := by sorry

attribute [defeq] GroundTheory.LocalField.WeilGroup.toGal_mk
