-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
-- name    : Kyprianou.Ch04.cor412_alltime_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:35:24.121069+00:00
-- url     : https://prove2.me/theorems/af141a36-9fef-581d-92fa-d37dcdef9264
-- title:
--   Measurability and nonnegativity of the all-time negative infimum on lower-bounded paths
-- statement:
--   Measurability and nonnegativity of the all-time negative infimum on lower-bounded paths.
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

theorem Kyprianou.Ch04.cor412_alltime_measurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    Measurable D ∧ ∀ w, 0 ≤ D w := by sorry
