-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_positive
-- name    : KSATSingleFlip.Connect.lemma_2_6_poisson_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:58:15.607196+00:00
-- url     : https://prove2.me/theorems/5a593863-63c5-46c7-82c1-c732e37cf9a3
-- title:
--   Lemma 2.6 Poisson-count bound for positive mean
-- statement:
--   Let the clause count have a positive Poisson mean νn, independently of a sequence of marks whose every finite prefix has the corresponding product law. Assume the observable lies in [0,n], changes by at most L ≥ 1 under a single insertion or deletion, and that √(νn) ≤ an/(4L), where 0 < a ≤ 1. Then its probability of falling an below its own expectation is at most 3 exp(−a²n/(128(ν+1)L²)). The explicit size condition is satisfied for all sufficiently large n; the zero-mean case is separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_poisson_positive {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
    (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hr : 0 < r) (hNlaw : Measure.map N P = poissonMeasure r)
    (X : ℕ → Ω → A) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ j, Measure.map (fun ω (i : Fin j) => X i.val ω) P = Measure.pi (fun _ : Fin j => D))
    (hind : ∀ j, IndepFun N (fun ω (i : Fin j) => X i.val ω) P)
    (F : List A → ℝ) (hF : ∀ j, Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hrν : (r:ℝ) = ν*n)
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L))
    (hbound : ∀ xs, 0 ≤ F xs ∧ F xs ≤ n)
    (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L) :
    P.real {ω | F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ≤
      (∫ ω, F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ∂P)-a*n} ≤
      3*Real.exp (-(a^2*n)/(128*(ν+1)*L^2)) := by sorry
