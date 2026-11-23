-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- name    : GroundTheory.LocalField.residueAlgEquiv_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:35.295032+00:00
-- url     : https://prove2.me/theorems/324ff0c9-837a-4dbb-b4b6-25c1b658df24
-- title:
--   Local Field: residue Alg Equiv residue
-- statement:
--   The Local Field construction uses the residue Alg Equiv residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L295-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L295-L298

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
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
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
variable (K L)

theorem GroundTheory.LocalField.residueAlgEquiv_residue (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    residueAlgEquiv K L σ (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L σ x) := by sorry

attribute [defeq] GroundTheory.LocalField.residueAlgEquiv_residue
