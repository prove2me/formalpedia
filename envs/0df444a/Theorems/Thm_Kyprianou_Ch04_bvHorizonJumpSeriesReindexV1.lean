-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvHorizonJumpSeriesReindexV1
-- name    : Kyprianou.Ch04.bvHorizonJumpSeriesReindexV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:50:26.407229+00:00
-- url     : https://prove2.me/theorems/35466708-f39d-46f0-ac64-5ba3816797f1
-- title:
--   Reindex atomic jump integrand on the compact horizon
-- statement:
--   Rewrite both sums over the full time type using indicators. At nonzero jumps the mark is the actual difference and the horizon restriction is equivalent to positive time at most t. At zero jumps the integrand vanishes.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.2; deterministic counting-measure auxiliary.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.bvHorizonJumpSeriesReindexV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (f : ℝ × ℝ → ℝ) (t : NNReal) :
    (∑' s : {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega},
      (Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ)).indicator
        (fun z => f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
          f (z.1, Xleft (Real.toNNReal z.1) omega))
        (((s : NNReal) : ℝ), X s omega - Xleft s omega)) =
      ∑' s : Set.Ioc (0 : NNReal) t,
        (f (((s : NNReal) : ℝ), X s omega) - f (((s : NNReal) : ℝ), Xleft s omega)) := by
  sorry
