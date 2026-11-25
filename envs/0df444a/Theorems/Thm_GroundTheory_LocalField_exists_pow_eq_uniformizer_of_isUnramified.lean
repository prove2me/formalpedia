-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_uniformizer_of_isUnramified
-- name    : GroundTheory.LocalField.exists_pow_eq_uniformizer_of_isUnramified
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:07.097514+00:00
-- url     : https://prove2.me/theorems/a241054c-baac-4ec1-8d71-ba2bf36db3a7
-- title:
--   Local Field: exists pow eq uniformizer of is Unramified
-- statement:
--   The Local Field construction uses the exists pow eq uniformizer of is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTame.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTame.lean#L82-L94

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
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
open scoped IntermediateField
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}

theorem GroundTheory.LocalField.exists_pow_eq_uniformizer_of_isUnramified (T : IntermediateField K L) [IsUnramified K T]
    (hf : residueDegree T L = 1) (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ramificationIndex T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by sorry
