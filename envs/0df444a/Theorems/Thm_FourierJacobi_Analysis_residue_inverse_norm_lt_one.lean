-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_residue_inverse_norm_lt_one
-- name    : FourierJacobi.Analysis.residue_inverse_norm_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:04.975736+00:00
-- url     : https://prove2.me/theorems/db27592c-8e8c-5400-ba25-0d127e3c8721
-- title:
--   Analysis: residue inverse norm lt one
-- statement:
--   The Analysis construction uses the residue inverse norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L127-L132
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L127-L132

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.residue_inverse_norm_lt_one (q : ℝ) (hq : 1 < q) :
    ‖(q : ℂ)⁻¹‖ < 1 := by sorry
