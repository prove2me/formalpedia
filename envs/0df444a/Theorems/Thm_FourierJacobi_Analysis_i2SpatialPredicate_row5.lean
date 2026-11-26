-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row5
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:44.157654+00:00
-- url     : https://prove2.me/theorems/ffeeb60b-0581-5e81-a94a-b28787fb8325
-- title:
--   Analysis: i2 Spatial Predicate row5
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L15-L15
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L15-L15

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row5 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 5 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := by sorry
