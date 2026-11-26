-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45NonnegativeTimeExtensionV2
-- name    : Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:17:44.926965+00:00
-- url     : https://prove2.me/theorems/3a4359bb-6d48-44bf-a3f1-7538d5cbeba0
-- title:
--   exercise45NonnegativeTimeExtensionV2
-- statement:
--   exercise45NonnegativeTimeExtensionV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (fun z : ℝ × ℝ => f (max z.1 0) z.2) := by
  sorry
