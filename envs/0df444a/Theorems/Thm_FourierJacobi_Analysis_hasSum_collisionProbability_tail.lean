-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionProbability_tail
-- name    : FourierJacobi.Analysis.hasSum_collisionProbability_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:17.381479+00:00
-- url     : https://prove2.me/theorems/cea7de63-a28c-42f0-aeba-a35bbba03a9d
-- title:
--   Analysis: has Sum collision Probability tail
-- statement:
--   The Analysis construction uses the has Sum collision Probability tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L79-L92
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L79-L92

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.hasSum_collisionProbability_tail (q : ℂ) (m : ℕ)
    (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => collisionProbability q (c + m + 1))
      ((q⁻¹) ^ (m + 1) * (1 - q⁻¹)⁻¹) := by sorry
