-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasDerivAt_inducingPower
-- name    : FourierJacobi.Analysis.hasDerivAt_inducingPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:52.678884+00:00
-- url     : https://prove2.me/theorems/c23d7946-9f87-52ce-a892-07869e7a59cb
-- title:
--   Analysis: has Deriv At inducing Power
-- statement:
--   The Analysis construction uses the has Deriv At inducing Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/IntertwinerDerivative.lean#L26-L34
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/IntertwinerDerivative.lean#L26-L34

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis

theorem FourierJacobi.Analysis.hasDerivAt_inducingPower (q : ℝ) (hq : 0 < q) :
    HasDerivAt (inducingPower q) (-2 * Real.log q / q) (1 / 2) := by sorry
