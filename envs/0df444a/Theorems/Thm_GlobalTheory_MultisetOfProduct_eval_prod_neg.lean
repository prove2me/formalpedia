-- Prove2me | Theorems.Thm_GlobalTheory_MultisetOfProduct_eval_prod_neg
-- name    : GlobalTheory.MultisetOfProduct.eval_prod_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:08.88861+00:00
-- url     : https://prove2.me/theorems/44380f3c-0316-487b-b125-c34081e6647a
-- title:
--   Multiset Of Product: eval prod neg
-- statement:
--   The Multiset Of Product construction uses the eval prod neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetEqOfProdAddEq.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetEqOfProdAddEq.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetEqOfProdAddEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultisetOfProduct
open Polynomial

theorem GlobalTheory.MultisetOfProduct.eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by sorry
