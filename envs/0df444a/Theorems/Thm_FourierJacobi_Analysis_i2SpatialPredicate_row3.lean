-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row3
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:06.593317+00:00
-- url     : https://prove2.me/theorems/45d0745c-456c-48b1-8cdf-30bc15e81cde
-- title:
--   Analysis: i2 Spatial Predicate row3
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L11-L11
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L11-L11

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row3 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 3 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := by sorry
