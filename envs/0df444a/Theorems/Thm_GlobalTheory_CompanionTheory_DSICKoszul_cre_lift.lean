-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_cre_lift
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.cre_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:47.007811+00:00
-- url     : https://prove2.me/theorems/c0bf9f80-1a7a-4e93-bf3b-3d62940717c4
-- title:
--   DSICKoszul: cre lift
-- statement:
--   The DSICKoszul construction uses the cre lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L143-L146

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

theorem GlobalTheory.CompanionTheory.DSICKoszul.cre_lift (i : NC ε) (T : Module.End ℂ Z) :
    Commute (cre i : Module.End ℂ (Ch ε Z)) (lift ε T) := by sorry
