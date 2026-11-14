-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_fixed_count
-- name    : KSATSingleFlip.Connect.lemma_2_6_fixed_count
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:34:27.773072+00:00
-- url     : https://prove2.me/theorems/88fb16d8-da12-4a0c-a4cd-ead102745fb0
-- title:
--   Fixed-count lower-tail bound for bounded clause replacements
-- statement:
--   Let j be positive, let the marked clauses be independent samples from a probability law, and let F be measurable. If replacing any one clause changes F by at most 2L, where L is at least one, then the probability that F falls at least u below its mean is at most exp(−u²/(2jL²)) for every u > 0. The paper obtains this replacement bound from its L bound on a single clause insertion or deletion. This statement is the fixed-count part of Lemma 2.6; it does not include the Poisson-count assertion.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_fixed_count {A : Type} [MeasurableSpace A] (j : ℕ) (hj : 1 ≤ j)
    (μ : Measure A) [IsProbabilityMeasure μ] (F : (Fin j → A) → ℝ)
    (hF : Measurable F) (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hreplace : ∀ (i : Fin j) (x : Fin j → A) (a : A),
      |F x - F (Function.update x i a)| ≤ 2*L) :
    Measure.pi (fun _ : Fin j => μ) {x | F x ≤ (∫ y, F y ∂(Measure.pi (fun _ : Fin j => μ))) - u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by sorry
