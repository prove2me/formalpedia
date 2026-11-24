-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_block_mem
-- name    : GlobalTheory.CompanionTheory.CapelliBlocks.block_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:51.764061+00:00
-- url     : https://prove2.me/theorems/76549569-6518-4656-b57d-fe8de8bd311e
-- title:
--   Capelli Blocks: block mem
-- statement:
--   The Capelli Blocks construction uses the block mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L109-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L109-L154

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

theorem GlobalTheory.CompanionTheory.CapelliBlocks.block_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {q p : ℕ}
    (r : Fin q ⊕ Fin p → Fin n) (hl : ∀ k, ε (r (Sum.inl k)) = false) (hr : ∀ k, ε (r (Sum.inr k)) = true)
    (u : ℂ) (v : V) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u v -
      (qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ))) v ∈
        pplus ε E := by sorry
