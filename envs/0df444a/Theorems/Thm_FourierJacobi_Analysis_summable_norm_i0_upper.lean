-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_upper
-- name    : FourierJacobi.Analysis.summable_norm_i0_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:00:11.849187+00:00
-- url     : https://prove2.me/theorems/65558b34-1b11-5800-ae2f-51a45c3554b5
-- title:
--   Analysis: summable norm i0 upper
-- statement:
--   The Analysis construction uses the summable norm i0 upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L348-L353
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L348-L353

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

theorem FourierJacobi.Analysis.summable_norm_i0_upper (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I0UpperRow neg => ‖i0Shell t d U V T p.val‖) := by sorry
