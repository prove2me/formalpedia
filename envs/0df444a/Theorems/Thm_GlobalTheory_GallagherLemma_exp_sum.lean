-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_exp_sum
-- name    : GlobalTheory.GallagherLemma.exp_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:40.18263+00:00
-- url     : https://prove2.me/theorems/b82898c9-e13c-434e-813b-0aedc30d78de
-- title:
--   Gallagher Lemma: exp sum
-- statement:
--   The Gallagher Lemma construction uses the exp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L99-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L99-L161

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

theorem GlobalTheory.GallagherLemma.exp_sum (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by sorry
