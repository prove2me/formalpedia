-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelN_measurable
-- name    : FourierJacobi.Valuations.kernelN_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:39.717404+00:00
-- url     : https://prove2.me/theorems/8552a246-fea0-42fb-ab08-a79602b5b23e
-- title:
--   Valuations: kernel N measurable
-- statement:
--   The Valuations construction uses the kernel N measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L230-L231
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L230-L231

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

theorem FourierJacobi.Valuations.kernelN_measurable : Measurable (kernelN K) := by sorry
