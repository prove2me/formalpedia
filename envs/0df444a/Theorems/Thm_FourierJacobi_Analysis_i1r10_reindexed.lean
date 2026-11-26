-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r10_reindexed
-- name    : FourierJacobi.Analysis.i1r10_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:46.024833+00:00
-- url     : https://prove2.me/theorems/793f8551-5c0c-561d-835b-7c78e43525aa
-- title:
--   Analysis: i1r10 reindexed
-- statement:
--   The Analysis construction uses the i1r10 reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L1429-L1448
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L1429-L1448

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

theorem FourierJacobi.Analysis.i1r10_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r10Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (T * V * t / d) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by sorry
