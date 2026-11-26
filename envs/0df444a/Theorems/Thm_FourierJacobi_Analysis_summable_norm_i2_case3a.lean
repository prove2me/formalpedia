-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case3a
-- name    : FourierJacobi.Analysis.summable_norm_i2_case3a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:08.673558+00:00
-- url     : https://prove2.me/theorems/6ac2c4e9-c034-48c7-bc53-06cae938b0b7
-- title:
--   Analysis: summable norm i2 case3a
-- statement:
--   The Analysis construction uses the summable norm i2 case3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L422-L429
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L422-L429

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

theorem FourierJacobi.Analysis.summable_norm_i2_case3a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 3 => ‖i2SpatialTerm q t d U V T 3 p.val‖) := by sorry
