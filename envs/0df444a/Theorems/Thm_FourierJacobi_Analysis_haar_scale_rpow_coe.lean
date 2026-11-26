-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haar_scale_rpow_coe
-- name    : FourierJacobi.Analysis.haar_scale_rpow_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:55.070802+00:00
-- url     : https://prove2.me/theorems/44449809-6397-4d18-829e-0c05ce7633d1
-- title:
--   Analysis: haar scale rpow coe
-- statement:
--   The Analysis construction uses the haar scale rpow coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L37-L40
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L37-L40

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.haar_scale_rpow_coe (q : ℝ) (hq : 0 < q) (k : ℤ) :
    (Real.rpow (q ^ (-k)) (3 / 2) : ℂ) = (inverseSqrt q : ℂ) ^ (3 * k) := by sorry
