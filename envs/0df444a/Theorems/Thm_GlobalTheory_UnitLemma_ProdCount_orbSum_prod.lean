-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_orbSum_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.orbSum_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:29:04.737795+00:00
-- url     : https://prove2.me/theorems/3b8fc58d-b14a-45d5-98e0-0bc789895920
-- title:
--   Prod Count: orb Sum prod
-- statement:
--   The Prod Count construction uses the orb Sum prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L87-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L87-L167

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

theorem GlobalTheory.UnitLemma.ProdCount.orbSum_prod (G₁ : Subgroup A₁ˣ) (G₂ : Subgroup A₂ˣ) (G : Subgroup (A₁ × A₂)ˣ)
    (hG : ∀ t, t ∈ G ↔ (MulEquiv.prodUnits t).1 ∈ G₁ ∧ (MulEquiv.prodUnits t).2 ∈ G₂)
    (X₁ : Set (Submodule O A₁)) (X₂ : Set (Submodule O A₂)) (X : Set (Submodule O (A₁ × A₂)))
    (hX : ∀ L₁ L₂, Submodule.prod L₁ L₂ ∈ X ↔ L₁ ∈ X₁ ∧ L₂ ∈ X₂)
    (hsplit : ∀ L ∈ X, ∃ L₁ L₂, L = Submodule.prod L₁ L₂) :
    orbSum O G X (fun _ => 1) = orbSum O G₁ X₁ (fun _ => 1) * orbSum O G₂ X₂ (fun _ => 1) := by sorry
