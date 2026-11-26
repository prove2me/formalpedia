-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r3ae_reindexed
-- name    : FourierJacobi.Analysis.i1r3ae_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:16.83815+00:00
-- url     : https://prove2.me/theorems/1e67f68b-043c-4ad3-90c4-b5d21def5724
-- title:
--   Analysis: i1r3ae reindexed
-- statement:
--   The Analysis construction uses the i1r3ae reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L268-L287
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L268-L287

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

theorem FourierJacobi.Analysis.i1r3ae_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r3aeEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by sorry
