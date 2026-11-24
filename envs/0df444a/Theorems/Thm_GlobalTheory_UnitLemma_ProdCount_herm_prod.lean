-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_herm_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.herm_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:29:04.614885+00:00
-- url     : https://prove2.me/theorems/1f6114c4-29f3-41cf-a1f8-8b77180a6f56
-- title:
--   Prod Count: herm prod
-- statement:
--   The Prod Count construction uses the herm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L210-L212

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

theorem GlobalTheory.UnitLemma.ProdCount.herm_prod (B₁ B₂ : InvAlg K) (x y z : B₁.A × B₂.A) :
    (B₁.prod B₂).herm x y z = B₁.herm x.1 y.1 z.1 + B₂.herm x.2 y.2 z.2 := by sorry
