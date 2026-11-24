-- Prove2me | Theorems.Thm_GlobalTheory_exists_short_family_adapted
-- name    : GlobalTheory.exists_short_family_adapted
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:14.940784+00:00
-- url     : https://prove2.me/theorems/1c4b3db4-53a1-40ff-8268-7060af6a2d14
-- title:
--   Global Theory: exists short family adapted
-- statement:
--   The Global Theory construction uses the exists short family adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L113-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L113-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.exists_short_family_adapted (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L) :
    ∃ b : Fin n → E, LinearIndependent ℝ b ∧
      (∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖b i‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by sorry
