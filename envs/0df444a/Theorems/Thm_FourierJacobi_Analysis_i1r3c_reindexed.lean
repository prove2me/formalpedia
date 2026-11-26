-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r3c_reindexed
-- name    : FourierJacobi.Analysis.i1r3c_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:34.789908+00:00
-- url     : https://prove2.me/theorems/31482040-7e81-4870-a7d2-a4b0248fa8ed
-- title:
--   Analysis: i1r3c reindexed
-- statement:
--   The Analysis construction uses the i1r3c reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L518-L537
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L518-L537

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

theorem FourierJacobi.Analysis.i1r3c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by sorry
