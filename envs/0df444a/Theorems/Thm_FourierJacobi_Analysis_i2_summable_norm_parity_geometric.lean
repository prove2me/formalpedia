-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_parity_geometric
-- name    : FourierJacobi.Analysis.i2_summable_norm_parity_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:22.823688+00:00
-- url     : https://prove2.me/theorems/9994d7a3-b078-441c-bc5f-6b11ce3b5093
-- title:
--   Analysis: i2 summable norm parity geometric
-- statement:
--   The Analysis construction uses the i2 summable norm parity geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L43-L52
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L43-L52

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_summable_norm_parity_geometric (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2‖) := by sorry
