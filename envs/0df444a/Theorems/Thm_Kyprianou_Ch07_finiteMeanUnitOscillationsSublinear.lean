-- Prove2me | Theorems.Thm_Kyprianou_Ch07_finiteMeanUnitOscillationsSublinear
-- name    : Kyprianou.Ch07.finiteMeanUnitOscillationsSublinear
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:11:22.142845+00:00
-- url     : https://prove2.me/theorems/6f1d1b5b-8d3f-45ae-b745-7e40c905956d
-- title:
--   Exercise 7.2(ii): maximal unit-block oscillations are negligible after scaling by n
-- statement:
--   With finite absolute first moment, unit-block Lévy maximal increments form a stationary integrable sequence; use a tail-sum/Borel-Cantelli bound to obtain Y_n/n -> 0 almost surely.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.2, printed p. 207; original PDF p. 216; source solution original PDF pp. 343–344. Exact conjunct isolated from the published complete Exercise 7.2 source proposition 1c79cede-86f1-4d46-b811-93526a74814d.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.finiteMeanUnitOscillationsSublinear
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun omega => |X 1 omega|) P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : Nat =>
        Kyprianou.Ch07.maximalUnitIncrement X n omega / (n : Real))
        atTop (nhds (0 : Real)) := by
  sorry
