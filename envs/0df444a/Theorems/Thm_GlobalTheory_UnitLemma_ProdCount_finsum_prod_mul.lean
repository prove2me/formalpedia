-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_finsum_prod_mul
-- name    : GlobalTheory.UnitLemma.ProdCount.finsum_prod_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:43.848797+00:00
-- url     : https://prove2.me/theorems/a7cd0745-ec97-4974-912c-59c71d3a7361
-- title:
--   Prod Count: finsum prod mul
-- statement:
--   The Prod Count construction uses the finsum prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L11-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L11-L34

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

theorem GlobalTheory.UnitLemma.ProdCount.finsum_prod_mul {α β : Type} (f : α → ℚ) (g : β → ℚ) :
    ∑ᶠ p : α × β, f p.1 * g p.2 = (∑ᶠ a, f a) * ∑ᶠ b, g b := by sorry
