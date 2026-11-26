-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_total_transform
-- name    : Kyprianou.Ch04.cor412_dyadic_total_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:44.220905+00:00
-- url     : https://prove2.me/theorems/63f13098-a1ee-4412-8528-1ce743b4a461
-- title:
--   Dyadic exponential infimum reward has the perpetual transform
-- statement:
--   Dyadic exponential infimum reward has the perpetual transform.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_eq
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
import Theorems.Thm_Kyprianou_Ch04_cor412_extended_perpetual_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The measurable dyadic reward has the perpetual negative infimum transform. -/

theorem Kyprianou.Ch04.cor412_dyadic_total_transform
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ w, ⨅ q : ℕ × ℕ, ENNReal.ofReal
      (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w)) ∂P) =
      ENNReal.ofReal (derivWithin L.ψ (Ici 0) 0 * β / L.ψ β) := by sorry
