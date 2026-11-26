-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2Case3a_cartan
-- name    : FourierJacobi.Analysis.i2Case3a_cartan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:16.25402+00:00
-- url     : https://prove2.me/theorems/7c2ea942-7731-5218-b3a4-9d4050907993
-- title:
--   Analysis: i2 Case3a cartan
-- statement:
--   The Analysis construction uses the i2 Case3a cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Domains.lean#L157-L163
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Domains.lean#L157-L163

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

theorem FourierJacobi.Analysis.i2Case3a_cartan (p : I2SpatialRow 3) (c : ℕ) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = (4, -p.val.1-p.val.2.1-2) := by sorry
