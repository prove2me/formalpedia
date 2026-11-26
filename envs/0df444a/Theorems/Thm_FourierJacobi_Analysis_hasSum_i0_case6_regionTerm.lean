-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case6_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case6_regionTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:59:11.877216+00:00
-- url     : https://prove2.me/theorems/ca3ad2b9-a3f4-533b-83bc-84447f69eee4
-- title:
--   Analysis: has Sum i0 case6 region Term
-- statement:
--   Direct identification with row 5 of the existing fifty-row expression.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L419-L428
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L419-L428

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

theorem FourierJacobi.Analysis.hasSum_i0_case6_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm5 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by sorry
