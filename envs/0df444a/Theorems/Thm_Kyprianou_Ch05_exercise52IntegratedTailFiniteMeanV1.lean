-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailFiniteMeanV1
-- name    : Kyprianou.Ch05.exercise52IntegratedTailFiniteMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:23.728891+00:00
-- url     : https://prove2.me/theorems/0a332939-d4d3-5004-8dc9-d12d30cff556
-- title:
--   The integrated-tail law has finite mean under the weighted-tail integrability condition
-- statement:
--   The integrated-tail law has finite mean under the weighted-tail integrability condition
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

theorem Kyprianou.Ch05.exercise52IntegratedTailFiniteMeanV1
    (nu : Measure ℝ) (m : ℝ) (hm : 0 < m)
    (hInt : IntegrableOn (fun z : ℝ => z * (nu (Ioi z)).toReal) (Ioi 0) volume) :
    Integrable (fun z : ℝ => z) (ascendingRecordJumpDistribution nu m) := by
  sorry
