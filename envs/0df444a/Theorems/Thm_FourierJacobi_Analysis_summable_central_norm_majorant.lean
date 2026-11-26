-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_central_norm_majorant
-- name    : FourierJacobi.Analysis.summable_central_norm_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:14.134745+00:00
-- url     : https://prove2.me/theorems/e562bace-f92c-47c7-bbb0-b964497d5508
-- title:
--   Analysis: summable central norm majorant
-- statement:
--   The Analysis construction uses the summable central norm majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L27-L35
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L27-L35

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.summable_central_norm_majorant (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    Summable (fun p : LatticeIndex =>
      ∑ i : Fin 8, ‖weightedLatticeTerm q a b d T (i,r,p)‖) := by sorry
