-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_measurable
-- name    : Kyprianou.Ch04.kw47_esscher_grid_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:52:09.501499+00:00
-- url     : https://prove2.me/theorems/8511dab2-1c84-53fa-a7ea-3add35c0a13a
-- title:
--   Measurability of finite Esscher product-grid gains
-- statement:
--   For an arbitrary finite deterministic time grid, the predictable Esscher product gain is measurable because each process value is measurable and finite sums and products preserve measurability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7(i).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite deterministic left-point Esscher grid gain is measurable. -/

theorem Kyprianou.Ch04.kw47_esscher_grid_measurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real)
    (u : Nat → NNReal) (n : Nat) :
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha*L.X t w-L.ψ alpha*(t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha*runningSup L t w+L.ψ alpha*(t:Real))
    Measurable (fun w => ∑ i ∈ Finset.range n,
      H (u i) w * (E (u (i+1)) w-E (u i) w)) := by sorry
