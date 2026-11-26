-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case8a_reindexed
-- name    : FourierJacobi.Analysis.i2_case8a_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:58:54.1734+00:00
-- url     : https://prove2.me/theorems/ab8958d4-14e0-5bf7-8d0e-69f2d69a56b1
-- title:
--   Analysis: i2 case8a reindexed
-- statement:
--   The Analysis construction uses the i2 case8a reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1246-L1263
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1246-L1263

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

theorem FourierJacobi.Analysis.i2_case8a_reindexed (q t d U V T : ℂ) (n : Fin 2 × ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 19 (i2Case8aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 19) * (T * V) ^ n.1.val * (T * V * t / d) ^ n.2.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.2.1 * (t ^ 2) ^ n.2.2.2 := by sorry
