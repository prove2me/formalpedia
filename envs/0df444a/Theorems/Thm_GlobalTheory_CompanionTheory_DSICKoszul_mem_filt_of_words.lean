-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_of_words
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_of_words
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:50.974805+00:00
-- url     : https://prove2.me/theorems/7956bef8-6973-4e98-8f2c-6bef1332d2b4
-- title:
--   DSICKoszul: mem filt of words
-- statement:
--   The DSICKoszul construction uses the mem filt of words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L100-L109

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
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}

theorem GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_of_words (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z)
    (h : ∀ l : List ι, l.length = m → (l.map d).prod z = 0) : z ∈ filt d m := by sorry
