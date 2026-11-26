-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperC_eq_poincare
-- name    : FourierJacobi.Analysis.paperC_eq_poincare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:59.20617+00:00
-- url     : https://prove2.me/theorems/0ea77e36-517b-4db8-a20c-1c0a8a26f4da
-- title:
--   Analysis: paper C eq poincare
-- statement:
--   The Analysis construction uses the paper C eq poincare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L42-L47
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L42-L47

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperC_eq_poincare (q : ℝ) (hq : 0 ≤ q) :
    paperC q = poincare (inverseSqrt q : ℂ) := by sorry
