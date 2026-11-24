-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_gallagher
-- name    : GlobalTheory.GallagherLemma.gallagher
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:12.704932+00:00
-- url     : https://prove2.me/theorems/b57bb295-bc8c-49a4-9b72-7fd0fc55ded6
-- title:
--   Gallagher Lemma: gallagher
-- statement:
--   The Gallagher Lemma construction uses the gallagher property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L163-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L163-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma

theorem GlobalTheory.GallagherLemma.gallagher : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by sorry
