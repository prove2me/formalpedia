-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_actual_grid_correction_limit
-- name    : Kyprianou.Ch04.kw48_actual_grid_correction_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:36:38.286501+00:00
-- url     : https://prove2.me/theorems/db9baf11-85b9-598b-9272-473607d8ba0c
-- title:
--   Actual complex correction converges
-- statement:
--   Actual complex correction converges.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_actual_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_linear_sum_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_correction_cell
import Theorems.Thm_Kyprianou_Ch04_kw48_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_record_grid_limit
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual right-point product correction converges to the two
Stieltjes and time primitives on every vanishing-mesh grid. -/

theorem Kyprianou.Ch04.kw48_actual_grid_correction_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n) :
    Tendsto (fun n => C L Psi alpha beta (u n) (N n) w)
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w)-
        Psi alpha*(J L alpha beta b w-J L alpha beta a w))) := by sorry
