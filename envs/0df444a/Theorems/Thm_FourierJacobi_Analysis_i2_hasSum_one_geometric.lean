-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_hasSum_one_geometric
-- name    : FourierJacobi.Analysis.i2_hasSum_one_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:31:17.062796+00:00
-- url     : https://prove2.me/theorems/503c5f91-5c72-4d82-8239-dadd9b6557b9
-- title:
--   Analysis: i2 has Sum one geometric
-- statement:
--   The Analysis construction uses the i2 has Sum one geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L39-L41
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L39-L41

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_hasSum_one_geometric (C a : ℂ) (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => C * a ^ n) (C * (1 - a)⁻¹) := by sorry
