-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r3c_raw
-- name    : FourierJacobi.Analysis.summable_norm_i1r3c_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:35.393222+00:00
-- url     : https://prove2.me/theorems/f6d66bf8-f748-4d47-ae56-b23d8fb1a36d
-- title:
--   Analysis: summable norm i1r3c raw
-- statement:
--   The Analysis construction uses the summable norm i1r3c raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L550-L559
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L550-L559

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

theorem FourierJacobi.Analysis.summable_norm_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3CRow => ‖i1Raw t d U V T p.val depth‖) := by sorry
