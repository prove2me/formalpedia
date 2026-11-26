-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row21
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:10.974036+00:00
-- url     : https://prove2.me/theorems/d6219e2a-99a7-40be-9cdf-6c83fe0af35c
-- title:
--   Analysis: i2 Spatial Predicate row21
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L47-L47
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L47-L47

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row21 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 21 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := by sorry
