-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelMinorIndex_measurable
-- name    : FourierJacobi.Valuations.kernelMinorIndex_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:30.34915+00:00
-- url     : https://prove2.me/theorems/1c8b34ad-cbbf-4a8a-8382-9ef3911a46eb
-- title:
--   Valuations: kernel Minor Index measurable
-- statement:
--   The Valuations construction uses the kernel Minor Index measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L212-L228
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L212-L228

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

theorem FourierJacobi.Valuations.kernelMinorIndex_measurable : Measurable (kernelMinorIndex K) := by sorry
