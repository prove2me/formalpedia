-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6
-- name    : KSATSingleFlip.Connect.lemma_2_6
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:02:10.870631+00:00
-- url     : https://prove2.me/theorems/f996b794-3349-4572-88ce-7a646d1d5553
-- title:
--   Lemma 2.6: bounded differences for clause counts
-- statement:
--   For j ≥ 1 independent marked clauses drawn from a fixed law, a measurable observable that changes by at most L ≥ 1 under one clause insertion or deletion satisfies the paper’s lower-tail bound exp(−u²/(2jL²)). If instead the clause count is Poisson(νn), independent of the marks, the observable takes values in [0,n], and 0 < a ≤ 1, then for all sufficiently large n, with the threshold depending only on ν, L, and a, its lower tail at distance an below the expectation is at most 3 exp(−a²n/(128(ν+1)L²)). The formal statement models insertion at any list position, finite-prefix product laws and their independence from the count, including ν=0.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6 :
  (∀ (A : Type) [MeasurableSpace A] (D : Measure A) [IsProbabilityMeasure D]
      (F : List A → ℝ) (j : ℕ) (hj : 1 ≤ j)
      (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
      (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
      (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L),
      (Measure.pi (fun _ : Fin j => D)) {x | F (List.ofFn x) ≤
        (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => D)))-u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2)))) ∧
  (∀ (ν a L : ℝ), 0 ≤ ν → 0 < a → a ≤ 1 → 1 ≤ L →
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ (Ω A : Type) [MeasurableSpace Ω] [MeasurableSpace A]
        (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
        (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hNlaw : Measure.map N P = poissonMeasure r)
        (X : ℕ → Ω → A) (hX : ∀ i, Measurable (X i))
        (hlaw : ∀ j, Measure.map (fun ω (i : Fin j) => X i.val ω) P = Measure.pi (fun _ : Fin j => D))
        (hind : ∀ j, IndepFun N (fun ω (i : Fin j) => X i.val ω) P)
        (F : List A → ℝ) (hF : ∀ j, Measurable (fun x : Fin j → A => F (List.ofFn x)))
        (hrν : (r:ℝ) = ν*(n:ℝ))
        (hbound : ∀ xs, 0 ≤ F xs ∧ F xs ≤ (n:ℝ))
        (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L),
      P.real {ω | F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ≤
        (∫ ω, F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ∂P)-a*(n:ℝ)} ≤
        3*Real.exp (-(a^2*(n:ℝ))/(128*(ν+1)*L^2))) := by sorry
