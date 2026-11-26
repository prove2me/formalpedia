-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_geometric_norm_summable
-- name    : FourierJacobi.Analysis.geometric_norm_summable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:49:26.269408+00:00
-- url     : https://prove2.me/theorems/028601a0-23e9-5a30-b8e6-55d90625dfbf
-- title:
--   Analysis: geometric norm summable
-- statement:
--   Norm summability is proved from the real geometric series directly.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L143-L146
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L143-L146

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

theorem FourierJacobi.Analysis.geometric_norm_summable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z ^ n‖) := by sorry
