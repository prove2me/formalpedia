-- Prove2me | Theorems.Thm_GlobalTheory_exists_pow_le_span_of_fg_of_integers
-- name    : GlobalTheory.exists_pow_le_span_of_fg_of_integers
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:11.742701+00:00
-- url     : https://prove2.me/theorems/45f96bdf-c1aa-4a76-b726-bc6a5a748ab1
-- title:
--   Global Theory: exists pow le span of fg of integers
-- statement:
--   The Global Theory construction uses the exists pow le span of fg of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L25-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L25-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_pow_le_span_of_fg_of_integers {C : Type*} [Field C] {v : Valuation C NNReal}
    {O : Type*} [CommRing O] [Algebra O C] (hv : v.Integers O) {J : Ideal O} (hJ : J.FG)
    (hJ' : J ≠ ⊤) {a : O} (ha : v (algebraMap O C a) ≠ 0) :
    ∃ n : ℕ, J ^ n ≤ Ideal.span {a} := by sorry
