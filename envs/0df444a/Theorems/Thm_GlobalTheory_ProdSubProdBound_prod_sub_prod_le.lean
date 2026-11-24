-- Prove2me | Theorems.Thm_GlobalTheory_ProdSubProdBound_prod_sub_prod_le
-- name    : GlobalTheory.ProdSubProdBound.prod_sub_prod_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:40.042989+00:00
-- url     : https://prove2.me/theorems/6a3316f7-c5a2-4984-80f9-a3eef554399c
-- title:
--   Prod Sub Prod Bound: prod sub prod le
-- statement:
--   The Prod Sub Prod Bound construction uses the prod sub prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProdSubProdLe.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProdSubProdLe.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdSubProdLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProdSubProdBound

theorem GlobalTheory.ProdSubProdBound.prod_sub_prod_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}
    (ha : ∀ i, v (a i) ≤ 1) (hb : ∀ i, v (b i) ≤ 1) (hab : ∀ i, v (a i - b i) ≤ c) :
    v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c := by sorry
