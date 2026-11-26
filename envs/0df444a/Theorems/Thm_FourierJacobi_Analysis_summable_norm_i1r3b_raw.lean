-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r3b_raw
-- name    : FourierJacobi.Analysis.summable_norm_i1r3b_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:09.028471+00:00
-- url     : https://prove2.me/theorems/9fee5010-8692-4aaa-9b90-e39033b9c9cb
-- title:
--   Analysis: summable norm i1r3b raw
-- statement:
--   The Analysis construction uses the summable norm i1r3b raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L469-L478
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L469-L478

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem FourierJacobi.Analysis.summable_norm_i1r3b_raw (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3BRow => ‖i1Raw t d U V T p.val 0‖) := by sorry
