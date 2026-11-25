-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_map_fixedField
-- name    : GroundTheory.LocalField.lowerRamificationGroup_map_fixedField
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:37.635319+00:00
-- url     : https://prove2.me/theorems/bdea80a7-deaf-4dc9-90af-8ea1efc8cc7a
-- title:
--   Local Field: lower Ramification Group map fixed Field
-- statement:
--   The Local Field construction uses the lower Ramification Group map fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L148-L151

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (M : IntermediateField K L)

theorem GroundTheory.LocalField.lowerRamificationGroup_map_fixedField [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) (i : ℤ) :
    (lowerRamificationGroup (IntermediateField.fixedField H) L i).map
        (AlgEquiv.restrictScalarsHom K) = lowerRamificationGroup K L i ⊓ H := by sorry
