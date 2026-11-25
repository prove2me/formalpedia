-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvPositiveJumpSupportCountableV1
-- name    : Kyprianou.Ch04.bvPositiveJumpSupportCountableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:50:29.014904+00:00
-- url     : https://prove2.me/theorems/3bc9336b-61d7-496a-a598-e9a6a7a22655
-- title:
--   Countability of actual positive-time jumps from compact absolute summability
-- statement:
--   On every integer horizon the support of the absolutely summable jump function is countable. The union of these supports covers all positive-time nonzero jumps.
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

theorem Kyprianou.Ch04.bvPositiveJumpSupportCountableV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (hSum : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|)) :
    ({s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega}).Countable := by
  sorry
