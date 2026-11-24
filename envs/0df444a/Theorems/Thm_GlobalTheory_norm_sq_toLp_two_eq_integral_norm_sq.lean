-- Prove2me | Theorems.Thm_GlobalTheory_norm_sq_toLp_two_eq_integral_norm_sq
-- name    : GlobalTheory.norm_sq_toLp_two_eq_integral_norm_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:02.856268+00:00
-- url     : https://prove2.me/theorems/657c1992-6932-4a90-9022-53e2d607cd54
-- title:
--   Global Theory: norm sq to Lp two eq integral norm sq
-- statement:
--   The Global Theory construction uses the norm sq to Lp two eq integral norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariant.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalOfUniformlyAlmostInvariant.lean#L8-L19

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

theorem GlobalTheory.norm_sq_toLp_two_eq_integral_norm_sq {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by sorry
