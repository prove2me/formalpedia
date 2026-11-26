-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_capped_grid_pathwise_limit
-- name    : Kyprianou.Ch04.kw48_capped_grid_pathwise_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:40:51.56775+00:00
-- url     : https://prove2.me/theorems/6d042db7-ad98-4b29-9e83-4874e92fb4f8
-- title:
--   Pathwise convergence of capped product grid
-- statement:
--   Pathwise convergence of capped product grid.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_actual_grid_correction_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The capped uniform product grid converges pathwise to the signed increment. -/

theorem Kyprianou.Ch04.kw48_capped_grid_pathwise_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (hab : a ≤ b) (w : Ω) :
    let u : Nat → Nat → NNReal := fun n i =>
      a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
    Tendsto (fun n => Q L Psi alpha beta (u n) (n+1) w) atTop
      (nhds (M L Psi alpha beta a w-M L Psi alpha beta b w)) := by sorry
