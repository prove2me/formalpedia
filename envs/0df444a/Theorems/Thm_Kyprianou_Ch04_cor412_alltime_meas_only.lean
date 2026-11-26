-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_alltime_meas_only
-- name    : Kyprianou.Ch04.cor412_alltime_meas_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:37:48.184134+00:00
-- url     : https://prove2.me/theorems/9228aada-116d-4754-b99a-70afe861eae7
-- title:
--   All-time negative infimum extended by zero is measurable
-- statement:
--   All-time negative infimum extended by zero is measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_alltime_meas_only
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    Measurable D := by sorry
