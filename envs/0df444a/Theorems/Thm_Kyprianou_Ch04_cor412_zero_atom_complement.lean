-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_complement
-- name    : Kyprianou.Ch04.cor412_zero_atom_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:46:10.824964+00:00
-- url     : https://prove2.me/theorems/676043d2-8374-4c04-be97-3790cd10cc81
-- title:
--   Finite downward passage is the complement of the all-time infimum zero atom
-- statement:
--   Finite downward passage is the complement of the all-time infimum zero atom.
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

theorem Kyprianou.Ch04.cor412_zero_atom_complement
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0) :
    let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Omega → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    (P {w : Omega | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}).toReal =
      1 - (P {w : Omega | D w = 0}).toReal := by sorry
