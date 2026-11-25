-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
-- name    : Kyprianou.Ch04.bvPathJumpMeasureAtomicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:50:36.69424+00:00
-- url     : https://prove2.me/theorems/a4e0e7d9-aa07-4b36-9f4f-87cf3ddac31d
-- title:
--   Path jump measure is the atomic sum over its countable support
-- statement:
--   Use measurability on the countable subtype and equality on every measurable set. Unfold counting measure as a Dirac sum and compare the indicator terms.
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

theorem Kyprianou.Ch04.bvPathJumpMeasureAtomicV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (hJ : ({s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega}).Countable) :
    pathJumpMeasure X Xleft omega =
      Measure.sum (fun s : {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega} => Measure.dirac
        (((s : NNReal) : ℝ), X s omega - Xleft s omega)) := by
  sorry
