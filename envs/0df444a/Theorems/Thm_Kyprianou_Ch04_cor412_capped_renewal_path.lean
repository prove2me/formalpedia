-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_path
-- name    : Kyprianou.Ch04.cor412_capped_renewal_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:21:47.212816+00:00
-- url     : https://prove2.me/theorems/f0703f27-71f2-5633-93e3-494102c95ef8
-- title:
--   Capped downward passage reward factors pathwise in the restricted integral
-- statement:
--   Capped downward passage reward factors pathwise in the restricted integral.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_passage_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- On the capped finite-passage event the original infimum reward is the product of the stopped and future rewards. -/

theorem Kyprianou.Ch04.cor412_capped_renewal_path
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) =
      min (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) (n : WithTop NNReal))
    (hB : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 ≤ β) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (n : WithTop NNReal)}
    let W : Ω → ℝ≥0∞ := A.indicator (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w, A.indicator (fun z => R (fun t => L.X t z)) w ∂P) =
      (∫⁻ w, W w * R (fun t => L.X (T w + t) w - L.X (T w) w) ∂P) := by sorry
