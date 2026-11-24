-- Prove2me | Theorems.Thm_GlobalTheory_contDiff_prod_ofFn_coord
-- name    : GlobalTheory.contDiff_prod_ofFn_coord
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:55.717805+00:00
-- url     : https://prove2.me/theorems/ffc004e5-b733-43d6-a1d2-38a75e116031
-- title:
--   Global Theory: cont Diff prod of Fn coord
-- statement:
--   The Global Theory construction uses the cont Diff prod of Fn coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStable.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStable.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContDiffOfContinuousOneParameterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStable
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

theorem GlobalTheory.contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by sorry
