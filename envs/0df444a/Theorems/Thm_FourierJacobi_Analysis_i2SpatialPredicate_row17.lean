-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row17
-- name    : FourierJacobi.Analysis.i2SpatialPredicate_row17
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:43.167002+00:00
-- url     : https://prove2.me/theorems/08b6e1f0-892b-533d-9017-dcd253267586
-- title:
--   Analysis: i2 Spatial Predicate row17
-- statement:
--   The Analysis construction uses the i2 Spatial Predicate row17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L39-L39
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Predicates.lean#L39-L39

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2SpatialPredicate_row17 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 17 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := by sorry
