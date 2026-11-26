-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case2_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case2_regionTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:00:29.998065+00:00
-- url     : https://prove2.me/theorems/f6769fa6-92ee-4f2e-985a-8743d7f900a7
-- title:
--   Analysis: has Sum i0 case2 region Term
-- statement:
--   Direct identification with row 1 of the existing fifty-row expression.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L406-L416
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L406-L416

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.hasSum_i0_case2_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0PositiveRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm1 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by sorry
