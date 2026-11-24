-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_mem_X_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.mem_X_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:43.343944+00:00
-- url     : https://prove2.me/theorems/fb014ea2-81eb-4bb4-85e7-2aca561a4b85
-- title:
--   Prod Count: mem X prod
-- statement:
--   The Prod Count construction uses the mem X prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L214-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L214-L256

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
variable {K : UQ}

theorem GlobalTheory.UnitLemma.ProdCount.mem_X_prod (B₁ B₂ : InvAlg K) (x₁ : B₁.A) (x₂ : B₂.A) (L₁ : Submodule K.O B₁.A)
    (L₂ : Submodule K.O B₂.A) :
    L₁.prod L₂ ∈ (B₁.prod B₂).X (x₁, x₂) ↔ L₁ ∈ B₁.X x₁ ∧ L₂ ∈ B₂.X x₂ := by sorry
