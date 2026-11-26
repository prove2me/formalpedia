-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernel_indices_of_minima
-- name    : FourierJacobi.Valuations.kernel_indices_of_minima
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:44.252514+00:00
-- url     : https://prove2.me/theorems/045b6c22-32b8-4cf9-8d1e-71442c4470d7
-- title:
--   Valuations: kernel indices of minima
-- statement:
--   The Valuations construction uses the kernel indices of minima property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L118-L136
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L118-L136

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

theorem FourierJacobi.Valuations.kernel_indices_of_minima (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    (kernelEll K p, kernelB K p) = cartanIndices r k j h c := by sorry
