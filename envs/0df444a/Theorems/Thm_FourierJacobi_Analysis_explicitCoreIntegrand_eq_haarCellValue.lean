-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_eq_haarCellValue
-- name    : FourierJacobi.Analysis.explicitCoreIntegrand_eq_haarCellValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:05.129405+00:00
-- url     : https://prove2.me/theorems/58ea0113-910c-5411-b527-2b0e956d961b
-- title:
--   Analysis: explicit Core Integrand eq haar Cell Value
-- statement:
--   The independently defined integrand is exactly constant on each actual cell.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L51-L61
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L51-L61

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.explicitCoreIntegrand_eq_haarCellValue (q : ℝ) (a b d : ℂ) (T : ℝ)
    (r : ℤ) (z : K) (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    explicitCoreIntegrand K q a b d T z p = haarCellValue q a b d T r i := by sorry
