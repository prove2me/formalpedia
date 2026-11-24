-- Prove2me | Theorems.Thm_GlobalTheory_SymmProd_prod_collect
-- name    : GlobalTheory.SymmProd.prod_collect
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:47.639181+00:00
-- url     : https://prove2.me/theorems/63a90ccc-1065-4b6b-baeb-fdfd08c88b0e
-- title:
--   Symm Prod: prod collect
-- statement:
--   The Symm Prod construction uses the prod collect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L14-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymmProd
open scoped Matrix

theorem GlobalTheory.SymmProd.prod_collect {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by sorry
