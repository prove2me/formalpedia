-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case3d_reindexed
-- name    : FourierJacobi.Analysis.i2_case3d_reindexed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:58:24.126004+00:00
-- url     : https://prove2.me/theorems/5fd49117-4ed2-473e-9321-f82de48fe6ab
-- title:
--   Analysis: i2 case3d reindexed
-- statement:
--   The Analysis construction uses the i2 case3d reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L566-L583
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L566-L583

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

theorem FourierJacobi.Analysis.i2_case3d_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 6 (i2Case3dEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 1 * (T * U) ^ 0 * (T * V) ^ 3 * i2DepthMass q 6) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by sorry
