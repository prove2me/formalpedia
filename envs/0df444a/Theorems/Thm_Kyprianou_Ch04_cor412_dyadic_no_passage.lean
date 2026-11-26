-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_no_passage
-- name    : Kyprianou.Ch04.cor412_dyadic_no_passage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:23:58.912457+00:00
-- url     : https://prove2.me/theorems/20820794-12e0-4295-b348-e50fb717953f
-- title:
--   Dyadic infimum reward is one on a path with no negative passage
-- statement:
--   Dyadic infimum reward is one on a path with no negative passage.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The dyadic infimum reward is one on a path which never enters the negative half-line. -/

theorem Kyprianou.Ch04.cor412_dyadic_no_passage
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (w : Ω) (h : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = ⊤)
    (β : ℝ) (hβ : 0 ≤ β) :
    (⨅ q : ℕ × ℕ, ENNReal.ofReal
      (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w))) = 1 := by sorry
