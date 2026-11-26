-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_region
-- name    : FourierJacobi.Analysis.hasSum_i0_region
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:00:48.576032+00:00
-- url     : https://prove2.me/theorems/fe3a63c0-80df-5ff9-b113-5ccc37ada447
-- title:
--   Analysis: has Sum i0 region
-- statement:
--   Every source row equals its already-restored stored fraction. The inherited
--   four rows are reused verbatim, and the six others are proved above.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L515-L531
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L515-L531

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

theorem FourierJacobi.Analysis.hasSum_i0_region (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) (i : Fin 10) :
    HasSum (fun p : i0Region i => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by sorry
