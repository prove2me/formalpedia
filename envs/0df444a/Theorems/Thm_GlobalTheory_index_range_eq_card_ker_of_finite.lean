-- Prove2me | Theorems.Thm_GlobalTheory_index_range_eq_card_ker_of_finite
-- name    : GlobalTheory.index_range_eq_card_ker_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:19.53846+00:00
-- url     : https://prove2.me/theorems/1d26552a-ce07-47db-944a-b5eba4f88a21
-- title:
--   Global Theory: index range eq card ker of finite
-- statement:
--   The Global Theory construction uses the index range eq card ker of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.index_range_eq_card_ker_of_finite {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by sorry
