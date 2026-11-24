-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_word_tens
-- name    : GlobalTheory.CompanionTheory.DSCover.word_tens
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:48.179291+00:00
-- url     : https://prove2.me/theorems/3cfaa279-9c04-47a0-aaef-1028b69d837c
-- title:
--   DSCover: word tens
-- statement:
--   The DSCover construction uses the word tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordMonomial.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordMonomial.lean#L97-L108

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.DSCover.word_tens (z : V ⊗[ℂ] MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length →
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod z = 0 := by sorry
