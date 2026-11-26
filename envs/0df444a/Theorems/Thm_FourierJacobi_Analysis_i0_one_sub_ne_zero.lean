-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_one_sub_ne_zero
-- name    : FourierJacobi.Analysis.i0_one_sub_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:51.470406+00:00
-- url     : https://prove2.me/theorems/baa72e19-d2b2-511f-ac25-aff4741519fb
-- title:
--   Analysis: i0 one sub ne zero
-- statement:
--   A norm bound implies a genuine geometric denominator is nonzero.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L285-L288
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L285-L288

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

theorem FourierJacobi.Analysis.i0_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by sorry
