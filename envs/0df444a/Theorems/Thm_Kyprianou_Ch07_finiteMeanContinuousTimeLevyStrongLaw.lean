-- Prove2me | Theorems.Thm_Kyprianou_Ch07_finiteMeanContinuousTimeLevyStrongLaw
-- name    : Kyprianou.Ch07.finiteMeanContinuousTimeLevyStrongLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:11:13.398202+00:00
-- url     : https://prove2.me/theorems/d7dab685-c8a2-4844-8b52-047d53b8ee75
-- title:
--   Exercise 7.2(iii): continuous-time strong law with finite first absolute moment
-- statement:
--   Derive the full-time Lévy strong law from iid unit increments, the discrete strong law and the maximal unit-block control.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.2, printed p. 207; original PDF p. 216; source solution original PDF pp. 343–344. Exact conjunct isolated from the published complete Exercise 7.2 source proposition 1c79cede-86f1-4d46-b811-93526a74814d.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.finiteMeanContinuousTimeLevyStrongLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun omega => |X 1 omega|) P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega / (t : Real))
        atTop (nhds (∫ omega, X 1 omega ∂P)) := by
  sorry
