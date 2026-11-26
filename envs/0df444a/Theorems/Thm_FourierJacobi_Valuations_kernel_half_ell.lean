-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_half_ell
-- name    : FourierJacobi.Valuations.kernel_half_ell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:55.603784+00:00
-- url     : https://prove2.me/theorems/ae769cea-7da5-5351-9040-f1e25c298160
-- title:
--   Valuations: kernel half ell
-- statement:
--   The Valuations construction uses the kernel half ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L114-L116
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L114-L116

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

theorem FourierJacobi.Valuations.kernel_half_ell (p : KernelPoint K) : kernelEll K p / 2 = kernelN K p := by sorry
