-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_middle
-- name    : FourierJacobi.Analysis.summable_norm_i0_middle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:01:17.791806+00:00
-- url     : https://prove2.me/theorems/cac96bb0-5d49-45a1-a4cf-90413d128eb7
-- title:
--   Analysis: summable norm i0 middle
-- statement:
--   The Analysis construction uses the summable norm i0 middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L290-L298
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L290-L298

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

theorem FourierJacobi.Analysis.summable_norm_i0_middle (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I0MiddleRow neg => ‖i0Shell t d U V T p.val‖) := by sorry
