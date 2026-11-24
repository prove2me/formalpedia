-- Prove2me | Theorems.Thm_GlobalTheory_exists_short_basis_adapted_of_subset_span
-- name    : GlobalTheory.exists_short_basis_adapted_of_subset_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:20.254255+00:00
-- url     : https://prove2.me/theorems/2da6cec5-6663-4f61-9d7d-1a172ee76409
-- title:
--   Global Theory: exists short basis adapted of subset span
-- statement:
--   The Global Theory construction uses the exists short basis adapted of subset span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L150-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L150-L166

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

theorem GlobalTheory.exists_short_basis_adapted_of_subset_span (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L)
    (hspan : (L : Set E) ⊆ span ℝ (Set.range v)) :
    ∃ b : Basis (Fin n) ℤ L,
      (∀ s : ℕ, span ℤ ((fun i => (b i : E)) '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖(b i : E)‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by sorry
