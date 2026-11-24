-- Prove2me | Theorems.Thm_GlobalTheory_even_dotProduct_mulVec_of_two_dvd
-- name    : GlobalTheory.even_dotProduct_mulVec_of_two_dvd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:11.511344+00:00
-- url     : https://prove2.me/theorems/fd4281b7-4e1c-4a70-b0fe-2c4729d404f8
-- title:
--   Global Theory: even dot Product mul Vec of two dvd
-- statement:
--   The Global Theory construction uses the even dot Product mul Vec of two dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L402-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L402-L407

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
omit [DecidableEq n]

theorem GlobalTheory.even_dotProduct_mulVec_of_two_dvd (hb : ∀ i j, 2 ∣ b i j) (d : Matrix n n ℤ) (μ : n → ℤ) :
    Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ) := by sorry
