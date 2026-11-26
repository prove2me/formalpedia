-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haar_scale_rpow
-- name    : FourierJacobi.Analysis.haar_scale_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:59.458477+00:00
-- url     : https://prove2.me/theorems/6a1eb9b5-b539-5ac6-b7c0-fcc4f507cb97
-- title:
--   Analysis: haar scale rpow
-- statement:
--   The Analysis construction uses the haar scale rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L22-L35
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L22-L35

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.haar_scale_rpow (q : ℝ) (hq : 0 < q) (k : ℤ) :
    Real.rpow (q ^ (-k)) (3 / 2) = inverseSqrt q ^ (3 * k) := by sorry
