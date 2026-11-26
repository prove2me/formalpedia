-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r6b_raw
-- name    : FourierJacobi.Analysis.summable_norm_i1r6b_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:14.220981+00:00
-- url     : https://prove2.me/theorems/655425f2-8f58-41d6-8295-61c2d5087c11
-- title:
--   Analysis: summable norm i1r6b raw
-- statement:
--   The Analysis construction uses the summable norm i1r6b raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L879-L889
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L879-L889

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

theorem FourierJacobi.Analysis.summable_norm_i1r6b_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6BRow => ‖i1Raw t d U V T p.val depth‖) := by sorry
