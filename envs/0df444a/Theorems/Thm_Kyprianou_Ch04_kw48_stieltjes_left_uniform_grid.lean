-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_stieltjes_left_uniform_grid
-- name    : Kyprianou.Ch04.kw48_stieltjes_left_uniform_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:37:15.951545+00:00
-- url     : https://prove2.me/theorems/dc3fd1d1-234f-4487-9ad9-7ed8695c78a2
-- title:
--   Exact exercise Stieltjes sum converges
-- statement:
--   Exact exercise Stieltjes sum converges.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_S_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exact left-endpoint Stieltjes sums in the exercise
converge pathwise at every time to the record-level primitive. -/

theorem Kyprianou.Ch04.kw48_stieltjes_left_uniform_grid {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (t : NNReal) :
    Tendsto (fun n : Nat => ∑ k ∈ Finset.range n,
      let u : NNReal := t*(k:NNReal)/(n:NNReal)
      let v : NNReal := t*((k+1:Nat):NNReal)/(n:NNReal)
      Z L alpha beta u w *
        ((runningSup L v w-runningSup L u w : Real):Complex))
      atTop (nhds (S L beta t w)) := by sorry
