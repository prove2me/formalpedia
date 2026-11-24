-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_appLE_comp_appLE_of_section
-- name    : GlobalTheory.ProperFunctions.appLE_comp_appLE_of_section
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:23.41718+00:00
-- url     : https://prove2.me/theorems/dacae6af-5fba-4dec-ba96-996a09ae6fba
-- title:
--   Proper Functions: app LE comp app LE of section
-- statement:
--   The Proper Functions construction uses the app LE comp app LE of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L193-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.appLE_comp_appLE_of_section {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (U : X.Opens)
    (W : S.Opens) (hW : W ≤ e ⁻¹ᵁ U) :
    p.appLE ⊤ U (le_preimage_top p U) ≫ e.appLE U W hW =
      Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ W) := by sorry
