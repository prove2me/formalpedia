-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_geometric_denominator_ne
-- name    : FourierJacobi.Analysis.i2_geometric_denominator_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:19.870319+00:00
-- url     : https://prove2.me/theorems/5c479682-6c60-518b-92a3-8cb8ca62ef32
-- title:
--   Analysis: i2 geometric denominator ne
-- statement:
--   The Analysis construction uses the i2 geometric denominator ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L10-L14
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L10-L14

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_geometric_denominator_ne (z : ℂ) (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by sorry
