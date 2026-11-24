-- Prove2me | Theorems.Thm_GlobalTheory_sq_sum_exp_pair
-- name    : GlobalTheory.sq_sum_exp_pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:38.28188+00:00
-- url     : https://prove2.me/theorems/40eae4cf-e96b-4b8d-a2ba-23b8933981a5
-- title:
--   Global Theory: sq sum exp pair
-- statement:
--   The Global Theory construction uses the sq sum exp pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L409-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L409-L421

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

theorem GlobalTheory.sq_sum_exp_pair (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    {ι : Type*} [Fintype ι] (r : ι → n → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)) :
    (∑ k, Complex.exp (Real.pi * Complex.I *
        ((fun i => (r k i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (r k i : ℂ)))) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by sorry
