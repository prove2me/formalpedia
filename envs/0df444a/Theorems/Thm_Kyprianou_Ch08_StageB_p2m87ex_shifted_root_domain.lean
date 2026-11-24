-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87ex_shifted_root_domain
-- name    : Kyprianou.Ch08.StageB.p2m87ex_shifted_root_domain
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:30:49.744935+00:00
-- url     : https://prove2.me/theorems/35af48ef-aeff-451a-b8c0-d2d91fec1f69
-- title:
--   Esscher shifted exponent has largest right root
-- statement:
--   Transfer unboundedness from the proved source root-domain theorem and use convexity and continuity of the shifted exponent.
-- source:
--   Kyprianou (2006), Exercise 8.7(i); decomposition of af7546b2-54be-4df1-896f-3b885337ff41.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m87ex_shifted_root_domain
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (c q : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    IsScaleTransformDomainBridge (shiftedExponent ψ c) q := by
  sorry
