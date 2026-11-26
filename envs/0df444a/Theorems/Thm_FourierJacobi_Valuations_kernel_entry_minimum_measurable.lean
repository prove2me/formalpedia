-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_entry_minimum_measurable
-- name    : FourierJacobi.Valuations.kernel_entry_minimum_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:39.82047+00:00
-- url     : https://prove2.me/theorems/0e18b38c-f463-5ad7-8e83-1bf1ae44aae0
-- title:
--   Valuations: kernel entry minimum measurable
-- statement:
--   The Valuations construction uses the kernel entry minimum measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L164-L175
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L164-L175

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

theorem FourierJacobi.Valuations.kernel_entry_minimum_measurable {α : Type*} [MeasurableSpace α]
    (a x y z : α → K) (ha : Measurable a) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (g (a p) (x p) (y p) (z p))) := by sorry
