-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r8c_reindexed
-- name    : FourierJacobi.Analysis.i1r8c_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:33.070798+00:00
-- url     : https://prove2.me/theorems/378ab13f-b43e-5a34-bc30-6a57c3277869
-- title:
--   Analysis: i1r8c reindexed
-- statement:
--   The Analysis construction uses the i1r8c reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L1265-L1284
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L1265-L1284

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

theorem FourierJacobi.Analysis.i1r8c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r8cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by sorry
