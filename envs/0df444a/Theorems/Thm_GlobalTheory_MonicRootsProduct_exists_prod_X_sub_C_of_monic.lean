-- Prove2me | Theorems.Thm_GlobalTheory_MonicRootsProduct_exists_prod_X_sub_C_of_monic
-- name    : GlobalTheory.MonicRootsProduct.exists_prod_X_sub_C_of_monic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:13.475279+00:00
-- url     : https://prove2.me/theorems/e46e9f47-d7fe-5444-b91e-72fbd532ed7d
-- title:
--   Monic Roots Product: exists prod X sub C of monic
-- statement:
--   The Monic Roots Product construction uses the exists prod X sub C of monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsProdXSubCOfMonic.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsProdXSubCOfMonic.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.MonicRootsProduct

theorem GlobalTheory.MonicRootsProduct.exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by sorry
