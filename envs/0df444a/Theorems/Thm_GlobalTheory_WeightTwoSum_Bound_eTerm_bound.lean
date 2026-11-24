-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_Bound_eTerm_bound
-- name    : GlobalTheory.WeightTwoSum.Bound.eTerm_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:21.796832+00:00
-- url     : https://prove2.me/theorems/a4bad2de-f910-434f-bde8-670578a95d92
-- title:
--   Bound: e Term bound
-- statement:
--   The Bound construction uses the e Term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightTwoDerivativeEisensteinTermUniformBound.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightTwoDerivativeEisensteinTermUniformBound.lean#L12-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.WeightTwoSum GlobalTheory.WeightTwoSum.Bound

theorem GlobalTheory.WeightTwoSum.Bound.eTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by sorry
