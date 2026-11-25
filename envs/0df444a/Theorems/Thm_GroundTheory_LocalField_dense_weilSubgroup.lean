-- Prove2me | Theorems.Thm_GroundTheory_LocalField_dense_weilSubgroup
-- name    : GroundTheory.LocalField.dense_weilSubgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:59:39.487801+00:00
-- url     : https://prove2.me/theorems/5ca34d60-19ec-5c20-891f-b2bf0b9179fc
-- title:
--   Local Field: dense weil Subgroup
-- statement:
--   The Local Field construction uses the dense weil Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L85-L112

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

theorem GroundTheory.LocalField.dense_weilSubgroup : Dense (weilSubgroup K Ω : Set (Ω ≃ₐ[K] Ω)) := by sorry
