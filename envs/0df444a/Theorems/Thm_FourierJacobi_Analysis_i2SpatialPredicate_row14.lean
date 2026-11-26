-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row14
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row14
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:28.703382+00:00
-- url     : https://prove2.me/theorems/c95941af-3960-5d98-acb0-3bad5764eef0
-- title:
--   Analysis: i2 Spatial Predicate row14
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L33-L33
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L33-L33

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row14 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 14 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := by sorry
