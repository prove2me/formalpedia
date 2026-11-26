-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_nonzero
-- name    : FourierJacobi.Valuations.kernelShellCoordinates_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:51.020054+00:00
-- url     : https://prove2.me/theorems/0448136e-32b5-4359-9857-fe2901f1264f
-- title:
--   Valuations: kernel Shell Coordinates nonzero
-- statement:
--   At r≠0 the actual collision ratio determines the cancellation-depth input.
--   Off the collision locus the implication is vacuous and the index is independent
--   of c; the master measure weight separately forces c=0 there.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L67-L77
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L67-L77

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Valuations.kernelShellCoordinates_nonzero (a : Kˣ) (x y z : K)
    (r k j h : ℤ) (c : ℕ) (hr : r ≠ 0)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,z) r k j h c := by sorry
