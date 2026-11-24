-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_isLat_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.isLat_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:31.167247+00:00
-- url     : https://prove2.me/theorems/41121aa0-cee3-4b54-9835-4829239dce47
-- title:
--   Prod Count: is Lat prod
-- statement:
--   The Prod Count construction uses the is Lat prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L188-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L188-L204

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

theorem GlobalTheory.UnitLemma.ProdCount.isLat_prod (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂] (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    IsLat O E (L₁.prod L₂) ↔ IsLat O E L₁ ∧ IsLat O E L₂ := by sorry
