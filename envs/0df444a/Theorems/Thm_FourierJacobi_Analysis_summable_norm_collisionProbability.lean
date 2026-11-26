-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_collisionProbability
-- name    : FourierJacobi.Analysis.summable_norm_collisionProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:34.49665+00:00
-- url     : https://prove2.me/theorems/08c52670-e768-493f-bd28-80bd58d911aa
-- title:
--   Analysis: summable norm collision Probability
-- statement:
--   The Analysis construction uses the summable norm collision Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L107-L111
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L107-L111

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.summable_norm_collisionProbability (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q c‖) := by sorry
