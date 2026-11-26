-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_norm_le
-- name    : FourierJacobi.Analysis.explicitWeylKernel_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:18.234423+00:00
-- url     : https://prove2.me/theorems/6ff3794d-e6b4-4b64-925e-67f49541ac0e
-- title:
--   Analysis: explicit Weyl Kernel norm le
-- statement:
--   The elementary regular-parameter majorant in the brief, in t coordinates.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L94-L103
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L94-L103

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.explicitWeylKernel_norm_le (t : ℝ) (a b : ℂ) (p : KernelPoint K)
    (ht : 0 ≤ t) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (t : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (t : ℂ) a b i‖) / poincare t) *
        t ^ (3 * kernelEll K p + 4 * kernelB K p) := by sorry
