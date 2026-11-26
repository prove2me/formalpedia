-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_kernelShell_nonzero_locus
-- name    : FourierJacobi.Valuations.kernelShell_nonzero_locus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:24.286799+00:00
-- url     : https://prove2.me/theorems/a6a56488-1bfe-5f2c-b6b7-2f134c25a7b7
-- title:
--   Valuations: kernel Shell nonzero locus
-- statement:
--   The finite actual shell/collision hypotheses really exclude zero coordinates
--   and determinant zero; the discarded sets have not been assigned finite values.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L81-L91
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean#L81-L91

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Valuations.kernelShell_nonzero_locus (x y z : K) (r j h : ℤ) (c : ℕ)
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ y^2-x*z ≠ 0 := by sorry
