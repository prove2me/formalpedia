-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case1
-- name    : FourierJacobi.Analysis.hasSum_i0_case1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:38.050291+00:00
-- url     : https://prove2.me/theorems/3d3bb284-c709-583d-ac50-35a99f5c95de
-- title:
--   Analysis: has Sum i0 case1
-- statement:
--   The first infinite valuation sum of `I0eq3`, equal to the damped
--   version of `I0eqq1`. Its hypotheses prove convergence, not merely that
--   the displayed denominator is nonzero.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L189-L209
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L189-L209

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

theorem FourierJacobi.Analysis.hasSum_i0_case1 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (1 - d * T * V * t)⁻¹ := by sorry
