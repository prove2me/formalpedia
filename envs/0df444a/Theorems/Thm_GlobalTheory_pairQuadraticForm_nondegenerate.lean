-- Prove2me | Theorems.Thm_GlobalTheory_pairQuadraticForm_nondegenerate
-- name    : GlobalTheory.pairQuadraticForm_nondegenerate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:56.960827+00:00
-- url     : https://prove2.me/theorems/1f77bb20-0d47-431e-a3a0-c8a34270f744
-- title:
--   Global Theory: pair Quadratic Form nondegenerate
-- statement:
--   The Global Theory construction uses the pair Quadratic Form nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L334-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L334-L367

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

theorem GlobalTheory.pairQuadraticForm_nondegenerate (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    (x : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)
    (hx : ∀ y, QuadraticMap.polar (pairQuadraticForm hd hs he) x y = 0) : x = 0 := by sorry
