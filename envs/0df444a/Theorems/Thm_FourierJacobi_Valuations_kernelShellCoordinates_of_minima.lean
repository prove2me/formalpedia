-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_of_minima
-- name    : FourierJacobi.Valuations.kernelShellCoordinates_of_minima
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:32.842678+00:00
-- url     : https://prove2.me/theorems/aa60d677-d287-40aa-9484-bef3eb3169e7
-- title:
--   Valuations: kernel Shell Coordinates of minima
-- statement:
--   The Valuations construction uses the kernel Shell Coordinates of minima property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L29-L50
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L29-L50

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Valuations.kernelShellCoordinates_of_minima (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    KernelShellCoordinates K p r k j h c := by sorry
