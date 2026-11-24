-- Prove2me | Theorems.Thm_GlobalTheory_ratCircleChar_pairQuadraticForm_mk
-- name    : GlobalTheory.ratCircleChar_pairQuadraticForm_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:29.786801+00:00
-- url     : https://prove2.me/theorems/91f9ed6b-b496-4d23-a3dd-4bceed70c0ba
-- title:
--   Global Theory: rat Circle Char pair Quadratic Form mk
-- statement:
--   The Global Theory construction uses the rat Circle Char pair Quadratic Form mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L317-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L317-L332

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

theorem GlobalTheory.ratCircleChar_pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    ratCircleChar (pairQuadraticForm hd hs he (Submodule.Quotient.mk ν)) =
      Complex.exp (Real.pi * Complex.I *
        ((fun i => (ν i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (ν i : ℂ))) := by sorry
