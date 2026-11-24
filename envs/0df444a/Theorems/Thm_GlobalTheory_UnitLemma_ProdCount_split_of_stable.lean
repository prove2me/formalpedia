-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_split_of_stable
-- name    : GlobalTheory.UnitLemma.ProdCount.split_of_stable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:38.677088+00:00
-- url     : https://prove2.me/theorems/9899c57f-da86-483b-bb0d-d7967a1a0a2a
-- title:
--   Prod Count: split of stable
-- statement:
--   The Prod Count construction uses the split of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L169-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]

theorem GlobalTheory.UnitLemma.ProdCount.split_of_stable (g : A₁ × A₂) (he : ((1, 0) : A₁ × A₂) ∈ Algebra.adjoin O ({g} : Set (A₁ × A₂)))
    (L : Submodule O (A₁ × A₂)) (hL : ∀ y ∈ L, g * y ∈ L) : ∃ L₁ L₂, L = Submodule.prod L₁ L₂ := by sorry
