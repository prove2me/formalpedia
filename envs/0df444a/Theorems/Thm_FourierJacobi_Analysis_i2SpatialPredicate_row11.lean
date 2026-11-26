-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row11
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:09.919213+00:00
-- url     : https://prove2.me/theorems/a6fbb092-e50d-5c1e-b2ba-b235651c081f
-- title:
--   Analysis: i2 Spatial Predicate row11
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L27-L27
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L27-L27

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row11 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 11 p ↔ (p.1 = 0 ∧ -1 ≤ p.2.1 ∧ p.2.2 ≤ -2) := by sorry
