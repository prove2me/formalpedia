-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_height_eq
-- name    : FourierJacobi.Valuations.kernel_height_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:28.335794+00:00
-- url     : https://prove2.me/theorems/fd87340a-adf4-4cf8-a874-4ae70d49ec89
-- title:
--   Valuations: kernel height eq
-- statement:
--   The Valuations construction uses the kernel height eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L109-L112
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L109-L112

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

theorem FourierJacobi.Valuations.kernel_height_eq (p : KernelPoint K) :
    kernelHeight K p = -kernelEntryIndex K p := by sorry
