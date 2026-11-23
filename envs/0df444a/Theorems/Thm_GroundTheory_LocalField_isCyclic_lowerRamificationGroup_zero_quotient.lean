-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isCyclic_lowerRamificationGroup_zero_quotient
-- name    : GroundTheory.LocalField.isCyclic_lowerRamificationGroup_zero_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:03.058786+00:00
-- url     : https://prove2.me/theorems/d1af51dd-90ae-4c12-b385-1f2aae41a035
-- title:
--   Local Field: is Cyclic lower Ramification Group zero quotient
-- statement:
--   The Local Field construction uses the is Cyclic lower Ramification Group zero quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L55-L59

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
omit hϖ
variable (K L)

theorem GroundTheory.LocalField.isCyclic_lowerRamificationGroup_zero_quotient :
    IsCyclic (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by sorry
