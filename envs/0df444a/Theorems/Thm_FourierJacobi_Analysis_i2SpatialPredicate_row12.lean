-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row12
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:25.060798+00:00
-- url     : https://prove2.me/theorems/3bf7bfe0-5f9f-48ba-aae2-35d59e9bb087
-- title:
--   Analysis: i2 Spatial Predicate row12
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L29-L29
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L29-L29

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row12 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 12 p ↔ (p.1 = -1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := by sorry
