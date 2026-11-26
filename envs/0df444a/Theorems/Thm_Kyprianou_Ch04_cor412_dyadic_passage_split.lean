-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_passage_split
-- name    : Kyprianou.Ch04.cor412_dyadic_passage_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:17:34.782597+00:00
-- url     : https://prove2.me/theorems/41e11f27-fcfc-5ce3-92bc-316a834110fa
-- title:
--   Exponential perpetual infimum reward factors at a finite downward passage
-- statement:
--   Exponential perpetual infimum reward factors at a finite downward passage.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_before
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_contact
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_eq
import Theorems.Thm_Kyprianou_Ch04_cor412_infimum_decomp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The exponential infimum reward factors pathwise at a finite downward passage. -/

theorem Kyprianou.Ch04.cor412_dyadic_passage_split
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal))
    (hb : BddBelow (range (fun s : NNReal => L.X s w)))
    (β : ℝ) (hβ : 0 ≤ β) :
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    R (fun s => L.X s w) =
      ENNReal.ofReal (Real.exp (β * L.X t w)) *
        R (fun u => L.X (t + u) w - L.X t w) := by sorry
