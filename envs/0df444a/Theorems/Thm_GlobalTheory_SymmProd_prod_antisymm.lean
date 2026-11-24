-- Prove2me | Theorems.Thm_GlobalTheory_SymmProd_prod_antisymm
-- name    : GlobalTheory.SymmProd.prod_antisymm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:44.022049+00:00
-- url     : https://prove2.me/theorems/56aaa209-86b6-47cb-881f-6fb9c122b5e3
-- title:
--   Symm Prod: prod antisymm
-- statement:
--   The Symm Prod construction uses the prod antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L34-L40

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

theorem GlobalTheory.SymmProd.prod_antisymm {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by sorry
