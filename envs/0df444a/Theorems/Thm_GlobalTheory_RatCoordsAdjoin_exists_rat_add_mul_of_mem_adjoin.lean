-- Prove2me | Theorems.Thm_GlobalTheory_RatCoordsAdjoin_exists_rat_add_mul_of_mem_adjoin
-- name    : GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:32.654252+00:00
-- url     : https://prove2.me/theorems/0cf92a69-093c-4eed-8f07-6b02de46a073
-- title:
--   Rat Coords Adjoin: exists rat add mul of mem adjoin
-- statement:
--   The Rat Coords Adjoin construction uses the exists rat add mul of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRatAddMulOfMemAdjoin.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRatAddMulOfMemAdjoin.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRatAddMulOfMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RatCoordsAdjoin

theorem GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by sorry
