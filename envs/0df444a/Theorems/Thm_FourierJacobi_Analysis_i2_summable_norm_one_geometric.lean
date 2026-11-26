-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_one_geometric
-- name    : FourierJacobi.Analysis.i2_summable_norm_one_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:37.071118+00:00
-- url     : https://prove2.me/theorems/92fcbc31-948f-5d17-9831-1d879a168e26
-- title:
--   Analysis: i2 summable norm one geometric
-- statement:
--   The Analysis construction uses the i2 summable norm one geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L35-L37
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L35-L37

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_summable_norm_one_geometric (C a : ℂ) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => ‖C * a ^ n‖) := by sorry
