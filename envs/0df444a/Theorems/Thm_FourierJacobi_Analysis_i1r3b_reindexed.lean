-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r3b_reindexed
-- name    : FourierJacobi.Analysis.i1r3b_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:33.512061+00:00
-- url     : https://prove2.me/theorems/4e4969c3-098d-5c8c-b855-8449dab729db
-- title:
--   Analysis: i1r3b reindexed
-- statement:
--   The Analysis construction uses the i1r3b reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L437-L456
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L437-L456

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

theorem FourierJacobi.Analysis.i1r3b_reindexed (t d U V T : ℂ)  
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3bEquiv n).val 0 = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by sorry
