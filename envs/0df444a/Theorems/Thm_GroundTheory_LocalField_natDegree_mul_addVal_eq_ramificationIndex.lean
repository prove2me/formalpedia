-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natDegree_mul_addVal_eq_ramificationIndex
-- name    : GroundTheory.LocalField.natDegree_mul_addVal_eq_ramificationIndex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:53.602863+00:00
-- url     : https://prove2.me/theorems/1c90f29c-84ef-499f-b41e-e4b14cc093c0
-- title:
--   Local Field: nat Degree mul add Val eq ramification Index
-- statement:
--   The Local Field construction uses the nat Degree mul add Val eq ramification Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L92-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L92-L177

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.natDegree_mul_addVal_eq_ramificationIndex {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
    {α : 𝒪[L]} (hα : aeval α f = 0) :
    (f.natDegree : ℕ∞) * addVal 𝒪[L] α = ramificationIndex K L := by sorry
