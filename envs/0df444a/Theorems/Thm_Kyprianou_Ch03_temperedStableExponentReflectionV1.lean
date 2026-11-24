-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableExponentReflectionV1
-- name    : Kyprianou.Ch03.temperedStableExponentReflectionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:49:31.447029+00:00
-- url     : https://prove2.me/theorems/8455f7ae-a27c-484a-8a86-65f34b834586
-- title:
--   Reflected compensated Lévy kernel integral
-- statement:
--   Change variables under reflection. The truncation |x|<1 is reflection invariant, and the products of the Fourier variable and jump agree.
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableExponentReflectionV1
    (mu : Measure ℝ) (xi : ℝ) :
    (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂(mu.map (fun x : ℝ => -x))) =
    ∫ x, ProbabilityTheory.levyCompensatedIntegrand (-xi) x ∂mu := by sorry
