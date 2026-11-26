-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
-- name    : FourierJacobi.Analysis.i2Case10Equiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:28.17472+00:00
-- url     : https://prove2.me/theorems/6856921a-6fe4-460c-bbb7-747d5989ae76
-- title:
--   Analysis: i2 Case10 Equiv val
-- statement:
--   The Analysis construction uses the i2 Case10 Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Domains.lean#L675-L676
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Domains.lean#L675-L676

import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Tactic.FinCases
import Definitions.Def_FourierJacobi_Analysis_I2Domains
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.i2Case10Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case10Equiv n).val = (-(n.1 : ℤ), -(n.2.1 : ℤ)-2, -(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) := by sorry

attribute [defeq] FourierJacobi.Analysis.i2Case10Equiv_val
