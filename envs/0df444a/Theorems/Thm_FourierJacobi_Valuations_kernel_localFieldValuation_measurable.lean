-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_localFieldValuation_measurable
-- name    : FourierJacobi.Valuations.kernel_localFieldValuation_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:28.488813+00:00
-- url     : https://prove2.me/theorems/81b9b55d-79be-4c07-82ea-3929466b302e
-- title:
--   Valuations: kernel local Field Valuation measurable
-- statement:
--   Measurability of the normalized valuation, supplied by the actual integer
--   shell theorem, and used below to measure the actual entry and minor minima.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L161-L162
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L161-L162

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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Valuations.kernelField_t2Space
attribute [local instance] FourierJacobi.Valuations.kernelField_secondCountable

theorem FourierJacobi.Valuations.kernel_localFieldValuation_measurable : Measurable (localFieldValuation K) := by sorry
