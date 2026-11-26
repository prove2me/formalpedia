-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelB_measurable
-- name    : FourierJacobi.Valuations.kernelB_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:57.918245+00:00
-- url     : https://prove2.me/theorems/7af6abb1-b761-422a-a195-0aa23c6713d1
-- title:
--   Valuations: kernel B measurable
-- statement:
--   The Valuations construction uses the kernel B measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L233-L234
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L233-L234

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

theorem FourierJacobi.Valuations.kernelB_measurable : Measurable (kernelB K) := by sorry
