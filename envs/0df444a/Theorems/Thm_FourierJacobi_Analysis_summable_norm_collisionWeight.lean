-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_collisionWeight
-- name    : FourierJacobi.Analysis.summable_norm_collisionWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:34.352916+00:00
-- url     : https://prove2.me/theorems/1a1f113f-7653-4ea1-bb91-6ab938fa5d0a
-- title:
--   Analysis: summable norm collision Weight
-- statement:
--   The Analysis construction uses the summable norm collision Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L121-L128
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L121-L128

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.summable_norm_collisionWeight (q : ℂ) (r j h : ℤ)
    (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionWeight q r j h c‖) := by sorry
