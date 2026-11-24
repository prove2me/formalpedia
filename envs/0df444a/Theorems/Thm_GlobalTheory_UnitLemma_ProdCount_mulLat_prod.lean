-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_mulLat_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.mulLat_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:59.298825+00:00
-- url     : https://prove2.me/theorems/00d32c19-4a3d-4114-9f94-e53ab2e92111
-- title:
--   Prod Count: mul Lat prod
-- statement:
--   The Prod Count construction uses the mul Lat prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L49-L57

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

theorem GlobalTheory.UnitLemma.ProdCount.mulLat_prod (t : A₁ × A₂) (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    mulLat O t (L₁.prod L₂) = (mulLat O t.1 L₁).prod (mulLat O t.2 L₂) := by sorry
