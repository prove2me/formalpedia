-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric
-- name    : FourierJacobi.Analysis.hasSum_three_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:54.022134+00:00
-- url     : https://prove2.me/theorems/a72a9967-91c2-44be-94b2-9059f28bf520
-- title:
--   Analysis: has Sum three geometric
-- statement:
--   An absolutely convergent product of three geometric families, indexed
--   by an unordered product type rather than an iterated, potentially conditional,
--   sum. This is the analysis used after the explicit domain bijections.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L160-L184
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L160-L184

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

theorem FourierJacobi.Analysis.hasSum_three_geometric (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : ℕ × ℕ × ℕ => C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by sorry
