-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row7
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:01.458222+00:00
-- url     : https://prove2.me/theorems/abb486b8-6042-40b0-804c-a63df37a41af
-- title:
--   Analysis: i2 Spatial Predicate row7
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L19-L19
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L19-L19

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row7 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 7 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := by sorry
