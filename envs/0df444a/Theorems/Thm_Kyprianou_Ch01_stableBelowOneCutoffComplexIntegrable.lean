-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneCutoffComplexIntegrable
-- name    : Kyprianou.Ch01.stableBelowOneCutoffComplexIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:33:45.318752+00:00
-- url     : https://prove2.me/theorems/cda45300-bd98-4c50-859a-2f131bf0e14b
-- title:
--   Complex Bochner integrability of the positive stable below-one source cutoff moment
-- statement:
--   For 0<alpha<1, the complex small-jump power r^-alpha supported on r>0,r<1 is integrable over the positive halfline. Transfer already-Proved real integrability by continuous real embedding, then use the pinned set-indicator integrability equivalence.
-- source:
--   Kyprianou (2006) Exercise 1.4, source cutoff compensator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerIntegrable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneCutoffComplexIntegrable
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    IntegrableOn
      (fun r : ℝ => if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0)
      (Set.Ioi (0 : ℝ)) := by sorry
