-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
-- name    : GroundTheory.LocalField.ramificationQuotientToUnits_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:18.993624+00:00
-- url     : https://prove2.me/theorems/404fd8df-a18e-4feb-8f77-8623dc562e44
-- title:
--   Local Field: ramification Quotient To Units mk
-- statement:
--   The Local Field construction uses the ramification Quotient To Units mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationUnits.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationUnits.lean#L192-L194

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
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

theorem GroundTheory.LocalField.ramificationQuotientToUnits_mk (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationQuotientToUnits hϖ n (QuotientGroup.mk σ) = ramificationToUnits hϖ n σ := by sorry

attribute [defeq] GroundTheory.LocalField.ramificationQuotientToUnits_mk
