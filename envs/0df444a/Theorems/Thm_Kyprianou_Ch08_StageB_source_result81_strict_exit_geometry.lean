-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_geometry
-- name    : Kyprianou.Ch08.StageB.source_result81_strict_exit_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:23:09.228437+00:00
-- url     : https://prove2.me/theorems/3736905f-1c9a-4e17-a2d5-e5af0f53221a
-- title:
--   Finite strict exit values and exclusion of a finite tie
-- statement:
--   Right continuity puts the finite exit value on the closed side of the crossed boundary. The left limit and absence of positive jumps give equality at the upper crossing, and a simultaneous finite upper and lower crossing is inconsistent with a positive upper level.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Pathwise reduction of b0b69794-330e-4301-89b9-d19ecb9fa31f.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_strict_exit_geometry
    (f : ℝ≥0 → ℝ) (a : ℝ) (ha : 0 < a) (hstart : f 0 ≤ a)
    (hcad : IsCadlag f)
    (hjumps : ∀ (s : ℝ≥0) (l : ℝ), 0 < s →
      Tendsto f (nhdsWithin s (Iio s)) (nhds l) → f s ≤ l) :
    let L := tauMinus (fun s (_ : Unit) => f s) 0 ()
    let U := tauPlus (fun s (_ : Unit) => f s) a ()
    (∀ t : ℝ≥0, U = (t : WithTop ℝ≥0) → f t = a) ∧
      (L = U → L = ⊤) := by
  sorry
