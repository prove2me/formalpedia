-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_of_uniformly_almost_invariant_alt
-- name    : GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:13.192694+00:00
-- url     : https://prove2.me/theorems/535c922a-46e6-4c15-affe-b9c1186a4fcb
-- title:
--   T: finite Dimensional of uniformly almost invariant alt
-- statement:
--   The T construction uses the finite Dimensional of uniformly almost invariant alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariantStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)), (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K), (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) → FiniteDimensional ℂ E := by sorry
