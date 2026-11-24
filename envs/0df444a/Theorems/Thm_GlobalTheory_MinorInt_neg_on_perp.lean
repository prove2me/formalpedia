-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_neg_on_perp
-- name    : GlobalTheory.MinorInt.neg_on_perp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:39.465421+00:00
-- url     : https://prove2.me/theorems/d0a9292d-25b4-43ad-aa6a-052b902740fc
-- title:
--   Minor Int: neg on perp
-- statement:
--   The Minor Int construction uses the neg on perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L135-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L135-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.neg_on_perp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ) (hA : A.det ≠ 0)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re)
    (b : ι → ℂ) (d : κ → ℂ) :
    ∑ a, ‖b a‖ ^ 2 ≤ 2 * ∑ i, ‖(Aᴴ *ᵥ b - Cᴴ *ᵥ d) i‖ ^ 2 + ∑ c, ‖d c‖ ^ 2 := by sorry
