-- Prove2me | Theorems.Thm_GlobalTheory_T_hasFDerivAt_weightTwoDerivativeEisensteinTerm
-- name    : GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:57.608534+00:00
-- url     : https://prove2.me/theorems/f1fa730c-9f13-48a9-8ad7-5859be14b75a
-- title:
--   T: has FDeriv At weight Two Derivative Eisenstein Term
-- statement:
--   The T construction uses the has FDeriv At weight Two Derivative Eisenstein Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtWeightTwoDerivativeEisensteinTermStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtWeightTwoDerivativeEisensteinTermStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtWeightTwoDerivativeEisensteinTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtWeightTwoDerivativeEisensteinTermStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x) (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j + (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by sorry
