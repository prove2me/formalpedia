-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_fixed_count_independent_fiber
-- name    : KSATSingleFlip.Connect.fixed_count_independent_fiber
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:54:38.510371+00:00
-- url     : https://prove2.me/theorems/7b806fed-6258-49c3-88fc-ba1c4d45cb3c
-- title:
--   Fixed-count tail on an independent count fiber
-- statement:
--   Suppose an integer-valued clause count is independent of a vector of j independent clause marks, and the observable changes by at most L under inserting a mark. On the count-j fiber, its lower-tail probability is at most the probability of that fiber multiplied by the fixed-count concentration bound from Lemma 2.6. The theorem states this in a joint probability space without conditioning on a possibly null fiber.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.fixed_count_independent_fiber {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
    (N : Ω → ℕ) (j : ℕ) (hj : 1 ≤ j) (Q : Ω → Fin j → A)
    (hQ : Measurable Q) (hlaw : Measure.map Q P = Measure.pi (fun _ : Fin j => D))
    (hind : IndepFun N Q P) (F : List A → ℝ)
    (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a)-F xs| ≤ L) :
    P ({ω | N ω = j} ∩ {ω | F (List.ofFn (Q ω)) ≤
      (∫ x, F (List.ofFn x) ∂(Measure.pi (fun _ : Fin j => D)))-u}) ≤
      P {ω | N ω = j} * ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by sorry
