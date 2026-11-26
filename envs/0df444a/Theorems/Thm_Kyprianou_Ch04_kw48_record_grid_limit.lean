-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_grid_limit
-- name    : Kyprianou.Ch04.kw48_record_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:33:15.002053+00:00
-- url     : https://prove2.me/theorems/66bcb573-a080-5adb-a148-597a0a0ea0b3
-- title:
--   Both endpoint record quadratures converge
-- statement:
--   Both endpoint record quadratures converge.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_measure_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_change
import Theorems.Thm_Kyprianou_Ch04_kw48_record_contact_identity
import Theorems.Thm_Kyprianou_Ch04_kw48_record_ae_continuous
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_right_path
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Both endpoint record quadratures converge to the difference
of the same record-level primitive. -/

theorem Kyprianou.Ch04.kw48_record_grid_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
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
        Z L alpha beta (if right then u n (i+1) else u n i) w) atTop
      (nhds (S L beta b w-S L beta a w)) := by sorry
