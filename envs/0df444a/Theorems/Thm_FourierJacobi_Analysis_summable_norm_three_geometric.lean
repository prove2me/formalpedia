-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric
-- name    : FourierJacobi.Analysis.summable_norm_three_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:20.825496+00:00
-- url     : https://prove2.me/theorems/2c57f4b9-6b69-44c8-a0dc-2597280c3cec
-- title:
--   Analysis: summable norm three geometric
-- statement:
--   Absolute convergence of a product indexed by three free nonnegative
--   integers, proved without changing the order of conditionally convergent sums.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L150-L155
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L150-L155

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

theorem FourierJacobi.Analysis.summable_norm_three_geometric (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : ℕ × ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2‖) := by sorry
