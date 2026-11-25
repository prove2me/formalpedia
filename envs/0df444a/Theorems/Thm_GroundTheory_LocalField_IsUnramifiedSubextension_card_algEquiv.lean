-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_card_algEquiv
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.card_algEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:41.197872+00:00
-- url     : https://prove2.me/theorems/9a777474-c07b-4872-8456-0bb3dce566f1
-- title:
--   Is Unramified Subextension: card alg Equiv
-- statement:
--   The Is Unramified Subextension construction uses the card alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L90-L94

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

theorem GroundTheory.LocalField.IsUnramifiedSubextension.card_algEquiv {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by sorry
