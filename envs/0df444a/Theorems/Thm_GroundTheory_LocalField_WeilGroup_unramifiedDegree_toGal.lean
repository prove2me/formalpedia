-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_unramifiedDegree_toGal
-- name    : GroundTheory.LocalField.WeilGroup.unramifiedDegree_toGal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:19.532151+00:00
-- url     : https://prove2.me/theorems/fe6b4a8f-f5c8-5136-9885-2b565d0bf8a8
-- title:
--   Weil Group: unramified Degree to Gal
-- statement:
--   The Weil Group construction uses the unramified Degree to Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L166-L168

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

theorem GroundTheory.LocalField.WeilGroup.unramifiedDegree_toGal (σ : WeilGroup K Ω) :
    unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (((degree K Ω σ).toAdd : ℤ) : ℤ̂) := by sorry
