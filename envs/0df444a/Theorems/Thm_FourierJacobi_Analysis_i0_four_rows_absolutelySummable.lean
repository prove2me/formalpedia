-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_four_rows_absolutelySummable
-- name    : FourierJacobi.Analysis.i0_four_rows_absolutelySummable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:26.349092+00:00
-- url     : https://prove2.me/theorems/a909738b-e7e0-4a88-a574-af5490b6e860
-- title:
--   Analysis: i0 four rows absolutely Summable
-- statement:
--   Absolute convergence of all four original-domain families. The shared
--   ratio conditions are kept explicit, including the damping variable.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L445-L469
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L445-L469

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

theorem FourierJacobi.Analysis.i0_four_rows_absolutelySummable (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I0PositiveRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0PositiveRow true => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow true => ‖i0Shell t d U V T p.val‖) := by sorry
