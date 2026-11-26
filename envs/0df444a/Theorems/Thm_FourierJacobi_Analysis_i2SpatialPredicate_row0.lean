-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row0
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:39.09725+00:00
-- url     : https://prove2.me/theorems/1f2c2c7c-bb2a-4694-b968-7a218bc145fe
-- title:
--   Analysis: i2 Spatial Predicate row0
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L5-L5
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L5-L5

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row0 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 0 p ↔ (2 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2) := by sorry
