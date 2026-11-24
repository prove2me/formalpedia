-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFrac_prod_zpow_mul
-- name    : GlobalTheory.LaurentFrac.prod_zpow_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:15.844022+00:00
-- url     : https://prove2.me/theorems/55cc1f51-1ae7-424b-a47b-1ff661e01baf
-- title:
--   Laurent Frac: prod zpow mul
-- statement:
--   The Laurent Frac construction uses the prod zpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdZpowMul.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdZpowMul.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdZpowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFrac

theorem GlobalTheory.LaurentFrac.prod_zpow_mul {K : Type} [Field K] {I : Type} [Fintype I] (a : I → K) (N : I → ℤ)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, a i ^ N i) * ∏ i, a i ^ (-N i).toNat = ∏ i, a i ^ (N i).toNat := by sorry
