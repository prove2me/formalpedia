-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_centralWeightedTerm
-- name    : FourierJacobi.Analysis.hasSum_centralWeightedTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:25.212973+00:00
-- url     : https://prove2.me/theorems/4826e592-89f4-409b-9f97-29ed650d5191
-- title:
--   Analysis: has Sum central Weighted Term
-- statement:
--   The Analysis construction uses the has Sum central Weighted Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L37-L47
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L37-L47

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.hasSum_centralWeightedTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    HasSum (centralWeightedTerm q a b d T r) (centralLatticeCore q a b d T r) := by sorry
