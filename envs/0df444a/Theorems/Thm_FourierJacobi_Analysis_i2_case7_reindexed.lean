-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case7_reindexed
-- name    : FourierJacobi.Analysis.i2_case7_reindexed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:03.905524+00:00
-- url     : https://prove2.me/theorems/7de7d0f4-d9f7-4667-b193-93b1ff9d7f90
-- title:
--   Analysis: i2 case7 reindexed
-- statement:
--   The Analysis construction uses the i2 case7 reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1191-L1208
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1191-L1208

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

theorem FourierJacobi.Analysis.i2_case7_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 18 (i2Case7Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 18) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by sorry
