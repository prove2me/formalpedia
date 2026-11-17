-- Prove2me | Theorems.Thm_Kyprianou_Ch07_finiteMeanMaximalUnitOscillationsIntegrable
-- name    : Kyprianou.Ch07.finiteMeanMaximalUnitOscillationsIntegrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:11:07.233004+00:00
-- url     : https://prove2.me/theorems/f8618480-8e83-47c1-95f4-1fece73e2be9
-- title:
--   Exercise 7.2(i): finite-mean Lévy processes have integrable unit-block maxima
-- statement:
--   Under a finite first absolute moment, every maximal centred increment on an integer time block has finite expectation. Proved via the Lévy maximal inequality, truncation and stationary increments.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.2, printed p. 207; original PDF p. 216; source solution original PDF pp. 343–344. Exact conjunct isolated from the published complete Exercise 7.2 source proposition 1c79cede-86f1-4d46-b811-93526a74814d.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.finiteMeanMaximalUnitOscillationsIntegrable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun omega => |X 1 omega|) P) :
    ∀ n : Nat, Integrable (Kyprianou.Ch07.maximalUnitIncrement X n) P := by
  sorry
