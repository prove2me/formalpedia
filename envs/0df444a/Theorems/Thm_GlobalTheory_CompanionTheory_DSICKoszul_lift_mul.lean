-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_lift_mul
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.lift_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:51.59724+00:00
-- url     : https://prove2.me/theorems/272dd7b0-8b21-4384-9d7f-0fe57a48fb5c
-- title:
--   DSICKoszul: lift mul
-- statement:
--   The DSICKoszul construction uses the lift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L135-L136

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem GlobalTheory.CompanionTheory.DSICKoszul.lift_mul (S T : Module.End ℂ Z) :
    (lift ε (S * T) : Module.End ℂ (Ch ε Z)) = lift ε S * lift ε T := by sorry
