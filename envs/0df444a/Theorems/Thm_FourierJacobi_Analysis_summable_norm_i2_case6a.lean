-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6a
-- name    : FourierJacobi.Analysis.summable_norm_i2_case6a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:44.555541+00:00
-- url     : https://prove2.me/theorems/e646fc95-9c6c-4c9c-bf73-c4beb4e29847
-- title:
--   Analysis: summable norm i2 case6a
-- statement:
--   The Analysis construction uses the summable norm i2 case6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L753-L758
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L753-L758

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

theorem FourierJacobi.Analysis.summable_norm_i2_case6a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 9 => ‖i2SpatialTerm q t d U V T 9 p.val‖) := by sorry
