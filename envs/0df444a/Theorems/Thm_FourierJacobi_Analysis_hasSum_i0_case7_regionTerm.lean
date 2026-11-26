-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case7_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case7_regionTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:59:14.416093+00:00
-- url     : https://prove2.me/theorems/d58b595a-2689-5a82-a169-0632162ee0a5
-- title:
--   Analysis: has Sum i0 case7 region Term
-- statement:
--   Direct identification with row 6 of the existing fifty-row expression.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L431-L441
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L431-L441

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

theorem FourierJacobi.Analysis.hasSum_i0_case7_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0NegativeRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm6 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by sorry
