-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_martingale_from_grid_event_limit
-- name    : Kyprianou.Ch04.kw48_martingale_from_grid_event_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:46.972238+00:00
-- url     : https://prove2.me/theorems/a3b3d4d4-ac27-44c0-a53e-8a34089ce5af
-- title:
--   Complex martingale transfer from dominated predictable grids
-- statement:
--   Complex martingale transfer from dominated predictable grids.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_dominated_event_zero
import Theorems.Thm_Kyprianou_Ch04_kw48_martingale_of_event_increment_zero
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Conditional-centred approximants transfer their martingale
property to an adapted L1-dominated pathwise limit. -/

theorem Kyprianou.Ch04.kw48_martingale_from_grid_event_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → Complex)
    (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (Q : NNReal → NNReal → Nat → Ω → Complex)
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
