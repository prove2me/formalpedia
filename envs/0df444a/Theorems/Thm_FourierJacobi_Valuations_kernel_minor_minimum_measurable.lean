-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_minor_minimum_measurable
-- name    : FourierJacobi.Valuations.kernel_minor_minimum_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:46.967271+00:00
-- url     : https://prove2.me/theorems/4f893e95-7850-490a-a99e-417520ee1bc0
-- title:
--   Valuations: kernel minor minimum measurable
-- statement:
--   The Valuations construction uses the kernel minor minimum measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L177-L194
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L177-L194

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

theorem FourierJacobi.Valuations.kernel_minor_minimum_measurable {α : Type*} [MeasurableSpace α]
    (a x y z : α → K) (ha : Measurable a) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) (ha0 : ∀ p, a p ≠ 0) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (secondCompound (g (a p) (x p) (y p) (z p)))) := by sorry
