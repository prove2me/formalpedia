-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_finsum_mul_star_pow_eq_zero
-- name    : GlobalTheory.CuspGL.eq_zero_of_finsum_mul_star_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:54.251812+00:00
-- url     : https://prove2.me/theorems/53e12a99-9482-41bc-9d36-11c5bc6b1b74
-- title:
--   Cusp GL: eq zero of finsum mul star pow eq zero
-- statement:
--   The Cusp GL construction uses the eq zero of finsum mul star pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfFinsumMulStarPowEqZero.lean#L8-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfFinsumMulStarPowEqZero.lean#L8-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.eq_zero_of_finsum_mul_star_pow_eq_zero {K : Type} [Field K] (θ : K →* ℂ)
    (hθ : ∀ x y : K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : 0 < N) (c : K → ℂ)
    (h : ∀ l : ℕ, ∑ᶠ α ∈ {α : K | α ^ N = 1}, c α * star (θ α ^ l) = 0) :
    ∀ α ∈ {α : K | α ^ N = 1}, c α = 0 := by sorry
