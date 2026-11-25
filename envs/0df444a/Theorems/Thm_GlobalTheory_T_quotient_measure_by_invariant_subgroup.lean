-- Prove2me | Theorems.Thm_GlobalTheory_T_quotient_measure_by_invariant_subgroup
-- name    : GlobalTheory.T.quotient_measure_by_invariant_subgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:54.447875+00:00
-- url     : https://prove2.me/theorems/222a6c8a-b943-4dab-b8cf-57ad6d831620
-- title:
--   T: quotient measure by invariant subgroup
-- statement:
--   The T construction uses the quotient measure by invariant subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuotientMeasureByInvariantSubgroupStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuotientMeasureByInvariantSubgroupStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroup
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quotient_measure_by_invariant_subgroup : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by sorry
