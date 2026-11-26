-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r6a_reindexed
-- name    : FourierJacobi.Analysis.i1r6a_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:52.933411+00:00
-- url     : https://prove2.me/theorems/395cec69-a058-5df8-8b9c-b35a09042020
-- title:
--   Analysis: i1r6a reindexed
-- statement:
--   The Analysis construction uses the i1r6a reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L765-L784
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L765-L784

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

theorem FourierJacobi.Analysis.i1r6a_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r6aEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by sorry
