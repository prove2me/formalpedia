-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_full
-- name    : FourierJacobi.Analysis.summable_norm_i0_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:53.557119+00:00
-- url     : https://prove2.me/theorems/a27fe0cc-b5e4-4e7b-93a9-89d15f51b038
-- title:
--   Analysis: summable norm i0 full
-- statement:
--   Absolute convergence is established on the full independent lattice
--   before the regions are combined. This statement is stronger than existence
--   of an iterated sum.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L536-L555
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L536-L555

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem FourierJacobi.Analysis.summable_norm_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : ℤ × ℤ × ℤ => ‖i0Shell t d U V T p‖) := by sorry
