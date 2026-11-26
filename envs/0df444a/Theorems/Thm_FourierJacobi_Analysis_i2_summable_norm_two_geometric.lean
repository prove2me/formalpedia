-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_two_geometric
-- name    : FourierJacobi.Analysis.i2_summable_norm_two_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:26.346464+00:00
-- url     : https://prove2.me/theorems/0c17ef7c-7188-45ce-b7b9-f692bee76cab
-- title:
--   Analysis: i2 summable norm two geometric
-- statement:
--   The Analysis construction uses the i2 summable norm two geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L16-L20
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L16-L20

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by sorry
