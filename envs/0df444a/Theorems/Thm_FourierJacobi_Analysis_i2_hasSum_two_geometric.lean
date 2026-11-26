-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_hasSum_two_geometric
-- name    : FourierJacobi.Analysis.i2_hasSum_two_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:31.516731+00:00
-- url     : https://prove2.me/theorems/29b44bd0-4214-532b-a900-4fdf42f25bca
-- title:
--   Analysis: i2 has Sum two geometric
-- statement:
--   The Analysis construction uses the i2 has Sum two geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L22-L33
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L22-L33

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by sorry
