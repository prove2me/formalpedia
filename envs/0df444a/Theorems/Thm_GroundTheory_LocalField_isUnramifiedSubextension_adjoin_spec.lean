-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin_spec
-- name    : GroundTheory.LocalField.isUnramifiedSubextension_adjoin_spec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:34.862499+00:00
-- url     : https://prove2.me/theorems/c649e5a7-6031-401e-a8b9-c52532f745e4
-- title:
--   Local Field: is Unramified Subextension adjoin spec
-- statement:
--   The Local Field construction uses the is Unramified Subextension adjoin spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L151-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L151-L159

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]

theorem GroundTheory.LocalField.isUnramifiedSubextension_adjoin_spec {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by sorry
