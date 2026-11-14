-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_expected_count_step_bound
-- name    : KSATSingleFlip.Connect.expected_count_step_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:53:34.184871+00:00
-- url     : https://prove2.me/theorems/fda129ec-efc5-408e-ba8d-035c354256c9
-- title:
--   Appending a clause changes the fixed-count mean by at most L
-- statement:
--   For any coupled sequence of clause marks, if an observable changes by at most L when a clause is inserted, and its values at each fixed prefix length are integrable, then consecutive expected observable values differ by at most L. This establishes the fixed-count mean sensitivity used in the Poisson-count argument of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem KSATSingleFlip.Connect.expected_count_step_bound {Ω A : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → A) (F : List A → ℝ) (L : ℝ)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L)
    (hint : ∀ j, Integrable (fun ω => F (List.ofFn fun i : Fin j => X i.val ω)) μ)
    (j : ℕ) :
    |(∫ ω, F (List.ofFn fun i : Fin (j+1) => X i.val ω) ∂μ) -
     (∫ ω, F (List.ofFn fun i : Fin j => X i.val ω) ∂μ)| ≤ L := by sorry
