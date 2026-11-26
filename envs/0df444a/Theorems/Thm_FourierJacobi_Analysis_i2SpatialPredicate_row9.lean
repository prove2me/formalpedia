-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row9
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:56.325919+00:00
-- url     : https://prove2.me/theorems/c72a0a29-5675-585c-ad53-4649bc8127c5
-- title:
--   Analysis: i2 Spatial Predicate row9
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L23-L23
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L23-L23

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row9 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 9 p ↔ (p.1 = 0 ∧ 0 ≤ p.2.1 ∧ -1 ≤ p.2.2) := by sorry
