-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case1a_reindexed
-- name    : FourierJacobi.Analysis.i2_case1a_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:58:07.121736+00:00
-- url     : https://prove2.me/theorems/a5b0fb85-cac0-450b-96bb-036f4555ceb5
-- title:
--   Analysis: i2 case1a reindexed
-- statement:
--   The Analysis construction uses the i2 case1a reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L247-L264
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L247-L264

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem FourierJacobi.Analysis.i2_case1a_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 0 (i2Case1aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 0) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by sorry
