-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_Tm_stab
-- name    : GlobalTheory.CompanionTheory.CapelliBlocks.Tm_stab
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:17.524848+00:00
-- url     : https://prove2.me/theorems/bfe242b5-a2b2-44b2-aef6-55eb214bb2d0
-- title:
--   Capelli Blocks: Tm stab
-- statement:
--   The Capelli Blocks construction uses the Tm stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L97-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L97-L107

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CapelliBlocks.Tm_stab (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a : Fin n) {b : Fin n}
    (hb : ε b = false) (u : ℂ) : ∀ v ∈ pplus ε E, Tm E u a b v ∈ pplus ε E := by sorry
