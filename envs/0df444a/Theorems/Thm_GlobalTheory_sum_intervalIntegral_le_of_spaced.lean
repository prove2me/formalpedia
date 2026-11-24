-- Prove2me | Theorems.Thm_GlobalTheory_sum_intervalIntegral_le_of_spaced
-- name    : GlobalTheory.sum_intervalIntegral_le_of_spaced
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:45.385518+00:00
-- url     : https://prove2.me/theorems/001a07f3-6327-4256-b7c4-cfc75bccf6ae
-- title:
--   Global Theory: sum interval Integral le of spaced
-- statement:
--   The Global Theory construction uses the sum interval Integral le of spaced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIntervalIntegralLeOfSpaced.lean#L90-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIntervalIntegralLeOfSpaced.lean#L90-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory

theorem GlobalTheory.sum_intervalIntegral_le_of_spaced (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by sorry
