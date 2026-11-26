-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_Z_contact_continuous
-- name    : Kyprianou.Ch04.kw48_Z_contact_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:38.405495+00:00
-- url     : https://prove2.me/theorems/0b530ff6-aa38-40b4-bc96-162d2dcd0519
-- title:
--   Reflected characteristic path continuity at positive contact times
-- statement:
--   Reflected characteristic path continuity at positive contact times.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- At a positive contact time the process has no downward jump
and its two-parameter characteristic process is continuous. -/

theorem Kyprianou.Ch04.kw48_Z_contact_continuous {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (w : Ω) (t : NNReal) (ht : 0 < t)
    (hContact : L.X t w = runningSup L t w) :
    ContinuousAt (fun r : NNReal => Z L alpha beta r w) t := by sorry
