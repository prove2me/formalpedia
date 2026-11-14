-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_fixed_clause_count
-- name    : KSATSingleFlip.Connect.lemma_2_6_fixed_clause_count
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:37:14.01823+00:00
-- url     : https://prove2.me/theorems/c95028d3-1e21-438e-87f9-47a7820df35c
-- title:
--   Lemma 2.6: fixed marked-clause count
-- statement:
--   For j at least one independent marked clauses from a fixed probability law, suppose the observable is measurable and changes by at most L ≥ 1 under insertion of any one clause at any position (and hence also under deletion). Then for u > 0 the lower-tail probability at distance u below its mean is at most exp(−u²/(2jL²)). This is the fixed-count half of Lemma 2.6; the separate Poisson-count bound is not included.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_fixed_clause_count {A : Type} [MeasurableSpace A] (j : ℕ) (hj : 1 ≤ j)
    (μ : Measure A) [IsProbabilityMeasure μ] (F : List A → ℝ)
    (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L) :
    Measure.pi (fun _ : Fin j => μ) {x | F (List.ofFn x) ≤
      (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => μ))) - u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by sorry
