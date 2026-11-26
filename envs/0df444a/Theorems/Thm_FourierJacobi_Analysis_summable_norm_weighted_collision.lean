-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_weighted_collision
-- name    : FourierJacobi.Analysis.summable_norm_weighted_collision
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:23:01.257668+00:00
-- url     : https://prove2.me/theorems/22bd8ae5-df43-5617-be73-04156a27e708
-- title:
--   Analysis: summable norm weighted collision
-- statement:
--   The Analysis construction uses the summable norm weighted collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L148-L158
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L148-L158

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.summable_norm_weighted_collision {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (hq : ‖q⁻¹‖ < 1)
    (hf : Summable (fun p => ‖f p‖)) :
    Summable (fun p : ι × ℕ => ‖f p.1 * collisionWeight q r (j p.1) (h p.1) p.2‖) := by sorry
