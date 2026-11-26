-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_lower
-- name    : FourierJacobi.Analysis.summable_norm_i0_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:08.332412+00:00
-- url     : https://prove2.me/theorems/b568ff58-cb7f-549f-b017-0ecfc364f98f
-- title:
--   Analysis: summable norm i0 lower
-- statement:
--   The Analysis construction uses the summable norm i0 lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L313-L321
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L313-L321

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

theorem FourierJacobi.Analysis.summable_norm_i0_lower (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I0LowerRow neg => ‖i0Shell t d U V T p.val‖) := by sorry
