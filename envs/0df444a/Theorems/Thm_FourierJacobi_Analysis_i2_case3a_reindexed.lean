-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_case3a_reindexed
-- name    : FourierJacobi.Analysis.i2_case3a_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:58:14.901334+00:00
-- url     : https://prove2.me/theorems/ed8471dc-ffdf-4c4a-a4d7-ce40f02a0ab2
-- title:
--   Analysis: i2 case3a reindexed
-- statement:
--   The Analysis construction uses the i2 case3a reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L403-L420
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L403-L420

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

theorem FourierJacobi.Analysis.i2_case3a_reindexed (q t d U V T : ℂ) (n : Fin 2 × ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 3 (i2Case3aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) * (T * V * t ^ 2) ^ n.1.val * (d * T * V * t) ^ n.2.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.2.1 * (t ^ 2) ^ n.2.2.2 := by sorry
