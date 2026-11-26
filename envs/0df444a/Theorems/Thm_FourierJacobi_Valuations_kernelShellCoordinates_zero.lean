-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_zero
-- name    : FourierJacobi.Valuations.kernelShellCoordinates_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:46.039843+00:00
-- url     : https://prove2.me/theorems/9ca45816-df76-44c3-b05e-fd1c574bb687
-- title:
--   Valuations: kernel Shell Coordinates zero
-- statement:
--   At r=0 the actual central coordinate is zero and there is no collision depth.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L53-L62
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L53-L62

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Valuations.kernelShellCoordinates_zero (a : Kˣ) (x y : K) (k j h : ℤ)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,0) 0 k j h 0 := by sorry
