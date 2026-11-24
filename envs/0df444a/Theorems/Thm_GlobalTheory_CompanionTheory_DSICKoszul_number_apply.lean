-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_number_apply
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.number_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:28.884992+00:00
-- url     : https://prove2.me/theorems/c9077cef-140c-44ce-8a42-08868ec9f646
-- title:
--   DSICKoszul: number apply
-- statement:
--   The DSICKoszul construction uses the number apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L166-L171

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

theorem GlobalTheory.CompanionTheory.DSICKoszul.number_apply (x : Ch ε Z) (A : Finset (NC ε)) :
    ((∑ i : NC ε, (cre i * ann i : Module.End ℂ (Ch ε Z))) x) A = (A.card : ℂ) • x A := by sorry
