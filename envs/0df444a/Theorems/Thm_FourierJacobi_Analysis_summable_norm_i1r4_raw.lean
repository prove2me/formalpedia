-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r4_raw
-- name    : FourierJacobi.Analysis.summable_norm_i1r4_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:45.757731+00:00
-- url     : https://prove2.me/theorems/0ebe679b-805a-439e-b51d-7c5b14731c46
-- title:
--   Analysis: summable norm i1r4 raw
-- statement:
--   The Analysis construction uses the summable norm i1r4 raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L632-L642
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L632-L642

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

theorem FourierJacobi.Analysis.summable_norm_i1r4_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I1R4Row => ‖i1Raw t d U V T p.val depth‖) := by sorry
