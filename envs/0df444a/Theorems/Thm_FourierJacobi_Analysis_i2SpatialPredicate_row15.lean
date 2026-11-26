-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row15
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:36.762693+00:00
-- url     : https://prove2.me/theorems/5309426c-de93-44a6-bce0-c329dff00a0e
-- title:
--   Analysis: i2 Spatial Predicate row15
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L35-L35
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L35-L35

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row15 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 15 p ↔ (p.1 ≤ -2 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := by sorry
