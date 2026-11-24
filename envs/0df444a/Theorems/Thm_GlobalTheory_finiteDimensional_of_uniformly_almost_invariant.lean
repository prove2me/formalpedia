-- Prove2me | Theorems.Thm_GlobalTheory_finiteDimensional_of_uniformly_almost_invariant
-- name    : GlobalTheory.finiteDimensional_of_uniformly_almost_invariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:36.3468+00:00
-- url     : https://prove2.me/theorems/f5dba51c-7b84-4eb0-88eb-558cc6aeb831
-- title:
--   Global Theory: finite Dimensional of uniformly almost invariant
-- statement:
--   The Global Theory construction uses the finite Dimensional of uniformly almost invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariant.lean#L21-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariant.lean#L21-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.finiteDimensional_of_uniformly_almost_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by sorry
