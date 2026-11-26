-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperE_eq_closedCore
-- name    : FourierJacobi.Analysis.paperE_eq_closedCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:58.489258+00:00
-- url     : https://prove2.me/theorems/b026a2b1-77bd-58e9-bb41-832682033d73
-- title:
--   Analysis: paper E eq closed Core
-- statement:
--   The Analysis construction uses the paper E eq closed Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L49-L56
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L49-L56

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperE_eq_closedCore (q : ℝ) (hq : 0 ≤ q) (a b d : ℂ) :
    paperE q a b d = closedCore (inverseSqrt q : ℂ) a b d := by sorry
