-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
-- name    : Kyprianou.Ch04.cor412_positive_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:46.23771+00:00
-- url     : https://prove2.me/theorems/8971c5c5-4ace-472a-9616-5ff824b08adb
-- title:
--   Positive right mean bounds every positive secant and exponent
-- statement:
--   Positive right mean bounds every positive secant and exponent.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_positive_exponent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0) :
    let m := derivWithin L.ψ (Ici 0) 0
    (∀ b : ℝ, 0 < b → m ≤ L.ψ b / b) ∧
    (∀ b : ℝ, 0 < b → 0 < L.ψ b) := by sorry
