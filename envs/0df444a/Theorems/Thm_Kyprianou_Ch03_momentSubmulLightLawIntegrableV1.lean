-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSubmulLightLawIntegrableV1
-- name    : Kyprianou.Ch03.momentSubmulLightLawIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:30:41.385314+00:00
-- url     : https://prove2.me/theorems/78117cb3-1ae8-4189-b728-4292545c3893
-- title:
--   Submultiplicative exponential envelope gives light-law integrability
-- statement:
--   Use the proved exercise 3.3 exponential envelope g(x) ≤ a exp(b|x|) and nonnegativity to dominate g by an integrable positive function.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; shared reduction of submulMoment_forward and submulMoment_reverse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSubmulLightLawIntegrableV1
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : ∀ R : Real, 0 ≤ R →
      ∃ M : Real, ∀ x : Real, |x| ≤ R → g x ≤ M)
    (hnu : ∀ b : Real, 0 < b → Integrable (fun x : Real => Real.exp (b * |x|)) nu) :
    Integrable g nu := by sorry
