-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpBandAtZero
-- name    : Kyprianou.Ch02.compensatedSmallJumpBandAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:57:01.76674+00:00
-- url     : https://prove2.me/theorems/e86aaf86-053f-410a-848e-46a819270bac
-- title:
--   Compensated finite small-jump band vanishes identically at physical time zero
-- statement:
--   For every finite-cutoff epsilon and every sample point, the Chapter 2 compensated Poisson small-jump band is exactly zero at time zero. The random integral is over the empty interval (0,0], and the deterministic compensator is multiplied by zero. This pointwise statement is used when normalising an almost-sure small-jump uniform limit to have deterministic initial value M0=0.
-- source:
--   Kyprianou (2006), Chapter 2, small-jump compensated band definition

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedSmallJumpBandAtZero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (ω : Ω) :
    Kyprianou.compensatedSmallJumpBand P levyMeasure N ε 0 ω = 0 := by
  sorry
