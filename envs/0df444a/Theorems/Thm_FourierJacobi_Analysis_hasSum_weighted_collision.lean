-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_weighted_collision
-- name    : FourierJacobi.Analysis.hasSum_weighted_collision
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:27:52.550182+00:00
-- url     : https://prove2.me/theorems/a8c6b543-4cc1-4348-897d-e5b1e9ab8981
-- title:
--   Analysis: has Sum weighted collision
-- statement:
--   The Analysis construction uses the has Sum weighted collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L160-L170
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L160-L170

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.hasSum_weighted_collision {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (s : ℂ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hf : HasSum f s) (hfn : Summable (fun p => ‖f p‖)) :
    HasSum (fun p : ι × ℕ => f p.1 * collisionWeight q r (j p.1) (h p.1) p.2) s := by sorry
