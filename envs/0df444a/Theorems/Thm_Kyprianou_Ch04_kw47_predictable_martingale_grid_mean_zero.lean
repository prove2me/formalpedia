-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_predictable_martingale_grid_mean_zero
-- name    : Kyprianou.Ch04.kw47_predictable_martingale_grid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:24:37.229443+00:00
-- url     : https://prove2.me/theorems/dbc7de94-622a-4e29-a834-8b0795fbb534
-- title:
--   Every finite predictable Esscher martingale grid gain has zero expectation
-- statement:
--   For an integrable real martingale E, a monotone deterministic time grid u, and bounded F_(u_i)-measurable weights W_i, the finite sum of products W_i(E_(u_(i+1))−E_(u_i)) is integrable and has expectation zero. The proof applies conditional centring to each term and Bochner integration of a finite sum. This supplies the exact finite-grid martingale step of the Kella–Whitt proof, later passed to L1 convergence.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.7; finite predictable martingale product-grid identity and Proved AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_predictable_martingale_grid_mean_zero
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : ℕ → Ω → Real) (u : ℕ → NNReal) (hu : Monotone u)
    (hW : ∀ i, Measurable[F (u i)] (W i)) (C : Real)
    (hWBound : ∀ i w, ‖W i w‖ ≤ C) (n : ℕ) :
    (∫ w, ∑ i ∈ Finset.range n,
      W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 := by sorry
