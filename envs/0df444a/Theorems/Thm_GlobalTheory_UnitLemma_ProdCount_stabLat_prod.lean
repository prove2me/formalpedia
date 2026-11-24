-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_stabLat_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.stabLat_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:54.996044+00:00
-- url     : https://prove2.me/theorems/a2d6a0ce-8d84-45fb-b89d-f1c158d6171e
-- title:
--   Prod Count: stab Lat prod
-- statement:
--   The Prod Count construction uses the stab Lat prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L66-L76

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

theorem GlobalTheory.UnitLemma.ProdCount.stabLat_prod (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) (t : (A₁ × A₂)ˣ) :
    t ∈ stabLat O (L₁.prod L₂) ↔
      (MulEquiv.prodUnits t).1 ∈ stabLat O L₁ ∧ (MulEquiv.prodUnits t).2 ∈ stabLat O L₂ := by sorry
