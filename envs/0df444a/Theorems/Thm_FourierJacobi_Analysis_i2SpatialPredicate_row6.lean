-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row6
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:46.671557+00:00
-- url     : https://prove2.me/theorems/a19ae7b6-2478-5f8d-82fa-6e8a0c488da6
-- title:
--   Analysis: i2 Spatial Predicate row6
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L17-L17
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L17-L17

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row6 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 6 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := by sorry
