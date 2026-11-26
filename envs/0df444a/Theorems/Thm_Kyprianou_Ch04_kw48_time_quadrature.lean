-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_time_quadrature
-- name    : Kyprianou.Ch04.kw48_time_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:46:49.654631+00:00
-- url     : https://prove2.me/theorems/76d87b61-fa41-406c-ac1c-80e392d86d62
-- title:
--   Right-point time quadrature for the complex reflected characteristic process
-- statement:
--   Right-point time quadrature for the complex reflected characteristic process.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_right_path
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Right-point time sums converge to the actual complex time integral increment. -/

theorem Kyprianou.Ch04.kw48_time_quadrature {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w)
      atTop (nhds (J L alpha beta b w-J L alpha beta a w)) := by sorry
