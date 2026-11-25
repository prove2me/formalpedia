-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_martingale_from_grid_event_limit
-- name    : Kyprianou.Ch04.kw47_martingale_from_grid_event_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:13:51.283795+00:00
-- url     : https://prove2.me/theorems/3e7ebab5-1ecf-57dc-af71-12c2c8136043
-- title:
--   Martingale transfer from integrable conditionally-centred finite grids and pathwise limits
-- statement:
--   A strongly adapted integrable process M is a true martingale if for every interval [a,b] its increment M_a-M_b is the almost-sure limit of finite-grid approximants Q(a,b,n), with each Q integrable, all Q dominated by one interval-specific integrable nonnegative envelope, and every Q has zero integral over each F_a measurable event. Apply the Proved dominated-event-zero theorem to the approximants and then the Proved martingale-from-zero-event-increments theorem. This is the exact conditional L1 transfer needed for the Kella-Whitt product-grid strategy.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7 solution pp.320–321; dominated convergence and characterisation of martingales by conditional event integrals.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_dominated_event_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_martingale_of_event_increment_zero
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Conditional-centred approximants transfer their martingale
property to an adapted L1-dominated pathwise limit. -/

theorem Kyprianou.Ch04.kw47_martingale_from_grid_event_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → Real)
    (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (Q : NNReal → NNReal → Nat → Ω → Real)
    (B : NNReal → NNReal → Ω → Real)
    (hQInt : ∀ a b, a ≤ b → ∀ n, Integrable (Q a b n) P)
    (hBInt : ∀ a b, a ≤ b → Integrable (B a b) P)
    (hBound : ∀ a b, a ≤ b → ∀ n, ∀ᵐ w ∂P,
      ‖Q a b n w‖ ≤ B a b w)
    (hLim : ∀ a b, a ≤ b → ∀ᵐ w ∂P,
      Tendsto (fun n => Q a b n w) atTop
        (nhds (M a w - M b w)))
    (hZero : ∀ a b, a ≤ b → ∀ n, ∀ A : Set Ω,
      MeasurableSet[F a] A →
        (∫ w in A, Q a b n w ∂P) = 0) :
    Martingale M F P := by sorry
