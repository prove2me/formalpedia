-- Prove2me | Theorems.Thm_GlobalTheory_ProductOfFnSingle_prod_ofFn_eq_single
-- name    : GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:00.238524+00:00
-- url     : https://prove2.me/theorems/71e8e459-ff53-47cf-b4d5-3e58892f4113
-- title:
--   Product Of Fn Single: prod of Fn eq single
-- statement:
--   The Product Of Fn Single construction uses the prod of Fn eq single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdOfFnEqSingle.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdOfFnEqSingle.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdOfFnEqSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.ProductOfFnSingle

theorem GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by sorry
