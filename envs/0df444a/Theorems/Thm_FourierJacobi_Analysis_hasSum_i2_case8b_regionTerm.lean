-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case8b_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i2_case8b_regionTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:44.75323+00:00
-- url     : https://prove2.me/theorems/d4aa62ad-1064-476c-bc33-c9ee36bad4c4
-- title:
--   Analysis: has Sum i2 case8b region Term
-- statement:
--   The Analysis construction uses the has Sum i2 case8b region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1328-L1353
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1328-L1353

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

theorem FourierJacobi.Analysis.hasSum_i2_case8b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 20 => i2SpatialTerm q t d U V T 20 p.val)
      (i2RegionTerm 20 t d (T * U) (T * V)) := by sorry
