-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row24
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row24
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:16.605229+00:00
-- url     : https://prove2.me/theorems/e47a42fd-aca5-4301-9abb-ec1466da34ef
-- title:
--   Analysis: i2 Spatial Predicate row24
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L53-L53
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L53-L53

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row24 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 24 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.2 < p.2.1) := by sorry
