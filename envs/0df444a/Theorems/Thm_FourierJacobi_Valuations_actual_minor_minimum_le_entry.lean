-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_le_entry
-- name    : FourierJacobi.Valuations.actual_minor_minimum_le_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:47.727896+00:00
-- url     : https://prove2.me/theorems/56bd2d9b-7c84-4fa1-ad92-6ad517590daa
-- title:
--   Valuations: actual minor minimum le entry
-- statement:
--   The missing upper minor bound for the concrete core matrix.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L21-L45
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L21-L45

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]

theorem FourierJacobi.Valuations.actual_minor_minimum_le_entry (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) ≤ matrixMinimum v (g a x y z) := by sorry
