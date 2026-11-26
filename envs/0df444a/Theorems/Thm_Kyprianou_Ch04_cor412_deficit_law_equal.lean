-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_deficit_law_equal
-- name    : Kyprianou.Ch04.cor412_deficit_law_equal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T09:44:14.645988+00:00
-- url     : https://prove2.me/theorems/e1ad341e-b6fa-4c09-b7b5-9c813168158c
-- title:
--   Actual finite downward-passage position law equals reflected integrated-tail measure
-- statement:
--   The actual stopped-position law on the finite passage event equals the reflected integrated negative jump tail measure.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_actual_deficit_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_tail_law_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_passage_position_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_exp_law
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exp_law_unique
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The actual stopped-position measure equals the reflected integrated-tail density. -/

theorem Kyprianou.Ch04.cor412_deficit_law_equal {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}
    let κ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))
    (P.restrict A).map (fun w => L.X (finiteTime w) w) = κ.map (fun y => -y) := by sorry
