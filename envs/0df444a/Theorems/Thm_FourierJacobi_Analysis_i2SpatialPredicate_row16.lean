-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row16
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row16
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:41.58073+00:00
-- url     : https://prove2.me/theorems/49bb3a2a-7bdc-4b08-ac34-24f529c3e5ea
-- title:
--   Analysis: i2 Spatial Predicate row16
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L37-L37
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L37-L37

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row16 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 16 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := by sorry
