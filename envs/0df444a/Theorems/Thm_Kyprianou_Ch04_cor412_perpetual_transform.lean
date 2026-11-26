-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_perpetual_transform
-- name    : Kyprianou.Ch04.cor412_perpetual_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:47.011614+00:00
-- url     : https://prove2.me/theorems/071040b7-d1f0-58f4-bd64-fb481d7505ac
-- title:
--   All-time infimum transform from bounded running-infimum rewards
-- statement:
--   All-time infimum transform from bounded running-infimum rewards.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_perpetual_transform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hbounded : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (hNotAnti : ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 < β) (hψ : L.ψ β ≠ 0) :
    (∫ w, Real.exp (β * sInf (range (fun t => L.X t w))) ∂P) =
      max 0 (sInf ((fun b : ℝ => L.ψ b / b) '' Ioi 0)) * β / L.ψ β := by sorry
