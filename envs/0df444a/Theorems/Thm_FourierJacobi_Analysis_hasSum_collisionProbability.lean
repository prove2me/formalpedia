-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionProbability
-- name    : FourierJacobi.Analysis.hasSum_collisionProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:35.552857+00:00
-- url     : https://prove2.me/theorems/b8a53e4e-3fe7-4c09-9c86-68eb889049fa
-- title:
--   Analysis: has Sum collision Probability
-- statement:
--   The Analysis construction uses the has Sum collision Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L94-L105
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L94-L105

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.hasSum_collisionProbability (q : ℂ) (hq₀ : q ≠ 0)
    (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionProbability q) 1 := by sorry
