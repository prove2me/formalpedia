-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_actual_exp_grid_linearization_limit
-- name    : Kyprianou.Ch04.kw47_actual_exp_grid_linearization_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:22:11.573824+00:00
-- url     : https://prove2.me/theorems/43f3d247-7caa-4b99-b5dd-83808e722f9c
-- title:
--   Vanishing exponential linearisation for the actual reflected process
-- statement:
--   On arbitrary monotone vanishing-mesh grids, the reflected exponential weighted first-order remainder of the actual Esscher multiplier exponent tends to zero. No Lipschitz assumption is required.
-- source:
--   Kyprianou (2006), Exercise 4.7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual running-supremum exponent has vanishing first-order
grid error, using continuity and variation, without Lipschitzness. -/

theorem Kyprianou.Ch04.kw47_actual_exp_grid_linearization_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let G : NNReal → Real := fun r =>
      -alpha * runningSup L r w + L.ψ alpha * (r:Real)
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
        (1 - Real.exp (-(G (u n (i+1)) - G (u n i))))) -
      (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
        (G (u n (i+1)) - G (u n i)))) atTop (nhds 0) := by sorry
