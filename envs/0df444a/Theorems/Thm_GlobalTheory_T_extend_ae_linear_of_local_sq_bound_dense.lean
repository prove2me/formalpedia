-- Prove2me | Theorems.Thm_GlobalTheory_T_extend_ae_linear_of_local_sq_bound_dense
-- name    : GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:35.279048+00:00
-- url     : https://prove2.me/theorems/0696cb65-7145-4724-9c67-b072673f9316
-- title:
--   T: extend ae linear of local sq bound dense
-- statement:
--   The T construction uses the extend ae linear of local sq bound dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtendAeLinearOfLocalSqBoundDenseStatement.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtendAeLinearOfLocalSqBoundDenseStatement.lean#L6-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtendAeLinearOfLocalSqBoundDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtendAeLinearOfLocalSqBoundDenseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by sorry
