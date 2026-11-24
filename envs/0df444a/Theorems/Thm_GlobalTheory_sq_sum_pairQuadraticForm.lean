-- Prove2me | Theorems.Thm_GlobalTheory_sq_sum_pairQuadraticForm
-- name    : GlobalTheory.sq_sum_pairQuadraticForm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:28.738503+00:00
-- url     : https://prove2.me/theorems/9cdcd35f-8e15-4bec-be38-e90555932824
-- title:
--   Global Theory: sq sum pair Quadratic Form
-- statement:
--   The Global Theory construction uses the sq sum pair Quadratic Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L388-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L388-L398

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

theorem GlobalTheory.sq_sum_pairQuadraticForm (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    [Fintype ((n → ℤ) ⧸ LinearMap.range d.mulVecLin)] :
    (∑ x, ratCircleChar (pairQuadraticForm (by rintro h; simp [h] at hodd) hs he x)) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by sorry
