-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_qminor_sum
-- name    : GlobalTheory.CompanionTheory.CapelliBlocks.qminor_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:43.718052+00:00
-- url     : https://prove2.me/theorems/48e6880e-bd42-412e-b98a-c10b7cf0ae5b
-- title:
--   Capelli Blocks: qminor sum
-- statement:
--   The Capelli Blocks construction uses the qminor sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L24-L38

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

theorem GlobalTheory.CompanionTheory.CapelliBlocks.qminor_sum {A : Type} [Ring A] [Algebra ℂ A] {n q p : ℕ} (E : Fin n → Fin n → A)
    (r : Fin q ⊕ Fin p → Fin n) (u : ℂ) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u =
      ∑ σ : Perm (Fin q ⊕ Fin p), ((Perm.sign σ : ℤ) : A) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod) := by sorry
