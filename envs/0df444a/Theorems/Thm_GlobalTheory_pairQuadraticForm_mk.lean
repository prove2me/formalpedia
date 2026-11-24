-- Prove2me | Theorems.Thm_GlobalTheory_pairQuadraticForm_mk
-- name    : GlobalTheory.pairQuadraticForm_mk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:07.751265+00:00
-- url     : https://prove2.me/theorems/89f3af58-6f5c-49e4-bd2f-9c337d8d6d64
-- title:
--   Global Theory: pair Quadratic Form mk
-- statement:
--   The Global Theory construction uses the pair Quadratic Form mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L311-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L311-L315

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

theorem GlobalTheory.pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    pairQuadraticForm hd hs he (Submodule.Quotient.mk ν) =
      ((((fun i => (ν i : ℚ)) ⬝ᵥ (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
        fun i => (ν i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := by sorry
