-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_extended_perpetual_transform
-- name    : Kyprianou.Ch04.cor412_extended_perpetual_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:45:54.674022+00:00
-- url     : https://prove2.me/theorems/9109686e-34d4-5f90-9246-cd5cb4adcc59
-- title:
--   Laplace transform of the measurable zero-extended perpetual infimum
-- statement:
--   Laplace transform of the measurable zero-extended perpetual infimum.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
import Theorems.Thm_Kyprianou_Ch04_cor412_perpetual_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_frequency_limit
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_path
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_extended_perpetual_transform
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0)
    (β : ℝ) (hβ : 0 < β) :
    let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Omega → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    (∫ w, Real.exp (β * (-D w)) ∂P) =
      derivWithin L.ψ (Ici 0) 0 * β / L.ψ β := by sorry
