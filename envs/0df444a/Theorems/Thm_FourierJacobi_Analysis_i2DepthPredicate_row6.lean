-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row6
-- name    : FourierJacobi.Analysis.i2DepthPredicate_row6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:49.805142+00:00
-- url     : https://prove2.me/theorems/2eadc8c0-aae7-496b-b310-3630606034d5
-- title:
--   Analysis: i2 Depth Predicate row6
-- statement:
--   The Analysis construction uses the i2 Depth Predicate row6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L18-L18
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L18-L18

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2DepthPredicate_row6 (c : ℕ) : i2DepthPredicate 6 c ↔ (2 ≤ c) := by sorry
