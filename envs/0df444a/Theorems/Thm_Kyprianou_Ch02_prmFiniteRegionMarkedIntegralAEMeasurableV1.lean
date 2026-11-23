-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegralAEMeasurableV1
-- name    : Kyprianou.Ch02.prmFiniteRegionMarkedIntegralAEMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:06:14.671801+00:00
-- url     : https://prove2.me/theorems/e47a6363-b34c-4abe-aa75-50a5fd80c890
-- title:
--   A.e. measurability of finite-intensity marked Poisson integral at every fixed time
-- statement:
--   At every deterministic finite time, the full real-valued marked KLS Poisson integral on (0,t]×B is almost-everywhere measurable. Apply source-proved measurable_setLIntegral_N to its positive and negative mark parts, then the already Proved Chapter 2 simultaneous a.s. integrability theorem to use integral_eq_lintegral_pos_part_sub_lintegral_neg_part on a full-measure event. This proof does not require first-moment integrability ν nor full-sample measurability of exceptional paths. It is sufficient for the existing Proved general stationary-increments-of-positive-pairs theorem.
-- source:
--   Kyprianou (2006) Chapter 2; LevyStochCalc/Poisson/CompensatedProfileRaw.lean aestronglyMeasurable_setIntegral_cell and Proved prmFiniteRegionMarkedIntegrableAllTimesAEV1.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionMarkedIntegralAEMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ t : ℝ≥0, AEMeasurable (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) P := by sorry
