-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreIntegralPrefactor_mul_shell_volume
-- name    : FourierJacobi.Analysis.coreIntegralPrefactor_mul_shell_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:21.066904+00:00
-- url     : https://prove2.me/theorems/acc62c64-9a02-5c78-a8b0-9a9a40324021
-- title:
--   Analysis: core Integral Prefactor mul shell volume
-- statement:
--   The Analysis construction uses the core Integral Prefactor mul shell volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L90-L104
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L90-L104

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.coreIntegralPrefactor_mul_shell_volume (q : ℝ) (hq : 1 < q) (r : Fin 3) :
    coreIntegralPrefactor q r * (1 - (q : ℂ)⁻¹) ^ 3 =
      shellCoeff (q : ℂ) (r.val : ℤ) * (1 - (q : ℂ)⁻¹) ^ 2 := by sorry
