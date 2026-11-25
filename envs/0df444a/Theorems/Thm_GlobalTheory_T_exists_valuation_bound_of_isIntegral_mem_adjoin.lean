-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_valuation_bound_of_isIntegral_mem_adjoin
-- name    : GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:01.632147+00:00
-- url     : https://prove2.me/theorems/04b47ebe-d5ee-54ff-93f9-13fa1b8daf43
-- title:
--   T: exists valuation bound of is Integral mem adjoin
-- statement:
--   The T construction uses the exists valuation bound of is Integral mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegralStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegralStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by sorry
