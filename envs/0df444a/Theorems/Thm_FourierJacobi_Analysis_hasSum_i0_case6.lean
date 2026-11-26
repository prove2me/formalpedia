-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case6
-- name    : FourierJacobi.Analysis.hasSum_i0_case6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:00:18.98035+00:00
-- url     : https://prove2.me/theorems/a7878ed9-7742-4ddb-922a-35b7c1fc6d2e
-- title:
--   Analysis: has Sum i0 case6
-- statement:
--   Case 6, including the first strictly negative valuation shell.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L338-L361
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L338-L361

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

theorem FourierJacobi.Analysis.hasSum_i0_case6 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      ((T * V * t / d) / (1 - T * V * t / d)) := by sorry
