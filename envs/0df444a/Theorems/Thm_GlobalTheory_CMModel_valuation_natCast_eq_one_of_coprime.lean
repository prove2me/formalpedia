-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_valuation_natCast_eq_one_of_coprime
-- name    : GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:51.507872+00:00
-- url     : https://prove2.me/theorems/9606680b-e7db-4434-8d6a-81a7de8c7719
-- title:
--   CMModel: valuation nat Cast eq one of coprime
-- statement:
--   The CMModel construction uses the valuation nat Cast eq one of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationNatCastEqOneOfCoprime.lean#L5-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationNatCastEqOneOfCoprime.lean#L5-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationNatCastEqOneOfCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by sorry
