-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6aa_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i2_case6aa_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:08.077727+00:00
-- url     : https://prove2.me/theorems/9d1449d0-72e7-5486-977f-7711d7e8b676
-- title:
--   Analysis: has Sum i2 case6aa region Term
-- statement:
--   The Analysis construction uses the has Sum i2 case6aa region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L809-L830
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L809-L830

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

theorem FourierJacobi.Analysis.hasSum_i2_case6aa_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 10 => i2SpatialTerm q t d U V T 10 p.val)
      (i2RegionTerm 10 t d (T * U) (T * V)) := by sorry
