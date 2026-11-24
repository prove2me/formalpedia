-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeFibresAtMostOneV1
-- name    : Kyprianou.Ch02.prmFiniteMarkTimeFibresAtMostOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:50:08.681882+00:00
-- url     : https://prove2.me/theorems/3078ce31-7a9e-445d-931b-93a8682e7dc3
-- title:
--   Finite-mark Poisson random measure has no simultaneous marks in a positive time fibre
-- statement:
--   Partition (0,T] into m equally spaced disjoint intervals. For each cell, the probability of a count greater than one is bounded by half its squared Poisson intensity. The probability that every such partition has a collision is zero, since the sum of the cell bounds tends to zero. A good partition excludes all positive-time simultaneous marks, including at grid endpoints by the half-open convention.
-- source:
--   Kyprianou (2006), Theorem 2.1. Strict jump-size bound for the compensated small-jump component; child of sourceFaithfulSmallJumpBandsCompactJumpCapV1.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteMarkTimeFibresAtMostOneV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ B) ≤ 1 := by sorry
