-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_N_prod_of_idem
-- name    : GlobalTheory.UnitLemma.ProdCount.N_prod_of_idem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:29:10.23191+00:00
-- url     : https://prove2.me/theorems/45dc365f-880d-4713-a921-6288a09e5151
-- title:
--   Prod Count: N prod of idem
-- statement:
--   The Prod Count construction uses the N prod of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L258-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L258-L263

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

theorem GlobalTheory.UnitLemma.ProdCount.N_prod_of_idem (B₁ B₂ : InvAlg K)
    (he : ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)))
    (x₁ : B₁.A) (x₂ : B₂.A) : (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by sorry
