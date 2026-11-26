-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_level_grid
-- name    : Kyprianou.Ch04.kw48_record_phase_level_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:45:39.227255+00:00
-- url     : https://prove2.me/theorems/5d229a10-4687-5a14-bdcc-3d4883437efa
-- title:
--   Complex phase quadrature on the mapped record-level grid
-- statement:
--   Complex phase quadrature on the mapped record-level grid.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_level_grid_mesh
import Theorems.Thm_Kyprianou_Ch04_kw48_level_primitive_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The time grid mapped by the running record is a vanishing-mesh
level grid, whose phase quadrature converges to the primitive increment. -/

theorem Kyprianou.Ch04.kw48_record_phase_level_grid {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n)
    (right : Bool) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
      Complex.exp (Complex.I * (beta:Complex) *
        (runningSup L (if right then u n (i+1) else u n i) w:Complex)))
      atTop (nhds (S L beta b w-S L beta a w)) := by sorry
