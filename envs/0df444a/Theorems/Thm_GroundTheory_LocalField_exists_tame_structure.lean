-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_tame_structure
-- name    : GroundTheory.LocalField.exists_tame_structure
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:32.022097+00:00
-- url     : https://prove2.me/theorems/18aa264b-6a5c-4604-8fdc-83d8005e8adc
-- title:
--   Local Field: exists tame structure
-- statement:
--   The Local Field construction uses the exists tame structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTameStructure.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTameStructure.lean#L18-L32

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_tame_structure (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ T : IntermediateField K L, IsUnramified K T ∧
      Module.finrank K T = residueDegree K L ∧ residueDegree T L = 1 ∧
      ramificationIndex T L = ramificationIndex K L ∧
      Module.finrank T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by sorry
