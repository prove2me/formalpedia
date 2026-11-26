-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripTruncatedIntegrableV1
-- name    : Kyprianou.Ch05.positivePoissonStripTruncatedIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:07.587547+00:00
-- url     : https://prove2.me/theorems/5a1158b7-a5c9-43b7-99bb-e41d39e73556
-- title:
--   Truncated positive mark integral is integrable under time-mark intensity
-- statement:
--   Factor the truncation into the finite time-window indicator and the integrable truncated mark function on positive marks.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.positivePoissonStripTruncatedIntegrableV1
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t : ℝ) :
    Integrable (fun z : ℝ × ℝ => min (1 : ℝ)
      |(Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z|) ((volume : Measure ℝ).prod Pi) := by
  sorry
