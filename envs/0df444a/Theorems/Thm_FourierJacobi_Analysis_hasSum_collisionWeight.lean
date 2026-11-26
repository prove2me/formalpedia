-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionWeight
-- name    : FourierJacobi.Analysis.hasSum_collisionWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:26.707117+00:00
-- url     : https://prove2.me/theorems/711bb9ac-bc06-51ea-a24b-dcd852ecf18e
-- title:
--   Analysis: has Sum collision Weight
-- statement:
--   The Analysis construction uses the has Sum collision Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L113-L119
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L113-L119

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.hasSum_collisionWeight (q : ℂ) (r j h : ℤ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionWeight q r j h) 1 := by sorry
