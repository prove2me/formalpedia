-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_uncapped_renewal_factor
-- name    : Kyprianou.Ch04.cor412_uncapped_renewal_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:01.637542+00:00
-- url     : https://prove2.me/theorems/0863c8d6-87c6-4e7d-98f0-2912e0812d6f
-- title:
--   Uncapped defective renewal factorisation
-- statement:
--   Exhaust finite passage by deterministic caps to obtain the defective renewal factorisation.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_selector
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_union
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Exhaust the finite passage event by deterministic caps to obtain the defective renewal factor. -/

theorem Kyprianou.Ch04.cor412_uncapped_renewal_factor
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hB : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 ≤ β)
    (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w in A, R (fun t => L.X t w) ∂P) =
      (∫⁻ w in A, ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w)) ∂P) *
        (∫⁻ w, R (fun t => L.X t w) ∂P) := by sorry
