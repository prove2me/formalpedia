-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residue_integerAlgEquiv_of_mem_zero
-- name    : GroundTheory.LocalField.residue_integerAlgEquiv_of_mem_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:51.568483+00:00
-- url     : https://prove2.me/theorems/5fa5abd7-c3da-4c55-893e-db384040ab25
-- title:
--   Local Field: residue integer Alg Equiv of mem zero
-- statement:
--   The Local Field construction uses the residue integer Alg Equiv of mem zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L150-L153

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
variable {K L}
variable (K L)

theorem GroundTheory.LocalField.residue_integerAlgEquiv_of_mem_zero {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (x : 𝒪[L]) : residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] x := by sorry
