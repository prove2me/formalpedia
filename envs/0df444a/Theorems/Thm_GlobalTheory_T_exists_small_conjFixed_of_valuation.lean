-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_small_conjFixed_of_valuation
-- name    : GlobalTheory.T.exists_small_conjFixed_of_valuation
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:12.088805+00:00
-- url     : https://prove2.me/theorems/0e6d8226-1ded-4107-92b6-0b9aa49fc1ea
-- title:
--   T: exists small conj Fixed of valuation
-- statement:
--   The T construction uses the exists small conj Fixed of valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuationStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuationStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by sorry
