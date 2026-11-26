-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_actual_deficit_transform
-- name    : Kyprianou.Ch04.cor412_actual_deficit_transform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T09:08:07.101801+00:00
-- url     : https://prove2.me/theorems/3c806ec7-0933-58a4-93f3-6e7e52fc213a
-- title:
--   Defective Laplace transform of actual finite downward passage
-- statement:
--   The actual finite downward passage position has the defective Laplace transform obtained from the perpetual infimum renewal identity.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_contact
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_no_passage
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_total_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_uncapped_renewal_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_renewal_algebra
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_downwardPassageFiniteProbabilityBV
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Defective Laplace transform of the actual finite downward-passage position. -/

theorem Kyprianou.Ch04.cor412_actual_deficit_transform {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (β : ℝ) (hβ : 0 < β) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    (∫⁻ w in {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤},
      ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w)) ∂P) =
      ENNReal.ofReal (1 - L.ψ β / (L.drift * β)) := by sorry
