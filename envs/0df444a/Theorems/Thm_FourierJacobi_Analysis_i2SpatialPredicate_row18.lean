-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row18
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row18
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:45.449433+00:00
-- url     : https://prove2.me/theorems/94bd7b60-f1a5-41bd-8ab6-17faa7915a36
-- title:
--   Analysis: i2 Spatial Predicate row18
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L41-L41
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L41-L41

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row18 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 18 p ↔ (p.1 ≤ -1 ∧ 0 ≤ p.2.1 ∧ p.2.2 ≤ -1) := by sorry
