-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case10_reindexed
-- name    : FourierJacobi.Analysis.i2_case10_reindexed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:08.736699+00:00
-- url     : https://prove2.me/theorems/d27f7221-7518-569c-9443-47de9554ef91
-- title:
--   Analysis: i2 case10 reindexed
-- statement:
--   The Analysis construction uses the i2 case10 reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1520-L1537
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1520-L1537

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

theorem FourierJacobi.Analysis.i2_case10_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 24 (i2Case10Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 8 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 24) * (T * V * t / d) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by sorry
