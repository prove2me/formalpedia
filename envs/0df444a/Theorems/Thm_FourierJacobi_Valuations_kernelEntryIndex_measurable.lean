-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelEntryIndex_measurable
-- name    : FourierJacobi.Valuations.kernelEntryIndex_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:57.525968+00:00
-- url     : https://prove2.me/theorems/a81f175f-af5c-56d0-b7fe-595362b8a7e1
-- title:
--   Valuations: kernel Entry Index measurable
-- statement:
--   The Valuations construction uses the kernel Entry Index measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L196-L210
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L196-L210

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

theorem FourierJacobi.Valuations.kernelEntryIndex_measurable : Measurable (kernelEntryIndex K) := by sorry
