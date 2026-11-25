-- Prove2me | Theorems.Thm_GlobalTheory_exists_rapid_fourierSeries_of_int_periodic
-- name    : GlobalTheory.exists_rapid_fourierSeries_of_int_periodic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:02.484671+00:00
-- url     : https://prove2.me/theorems/ab8555d6-ced4-4682-8720-e98c0e69829d
-- title:
--   Global Theory: exists rapid fourier Series of int periodic
-- statement:
--   The Global Theory construction uses the exists rapid fourier Series of int periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRapidFourierSeriesOfIntPeriodic.lean#L38-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRapidFourierSeriesOfIntPeriodic.lean#L38-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real RealInnerProductSpace
open GlobalTheory

theorem GlobalTheory.exists_rapid_fourierSeries_of_int_periodic :
    ∀ (n : ℕ) (w : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ w →
      (∀ (ν : Fin n → ℤ) x, w (x + fun k => (ν k : ℝ)) = w x) →
      ∃ c : (Fin n → ℤ) → ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) ∧
        ∀ x, w x = ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) := by sorry
