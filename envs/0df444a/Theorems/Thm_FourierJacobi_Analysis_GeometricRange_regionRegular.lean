-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_GeometricRange_regionRegular
-- name    : FourierJacobi.Analysis.GeometricRange.regionRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:58.684414+00:00
-- url     : https://prove2.me/theorems/db48a8a6-274f-4f5c-aebb-1911fd6ff36f
-- title:
--   Geometric Range: region Regular
-- statement:
--   The Geometric Range construction uses the region Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L73-L78
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L73-L78

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.GeometricRange.regionRegular {t d U V T : ℂ}
    (h : GeometricRange t d U V T) : RegionRegular t d (T * U) (T * V) := by sorry
