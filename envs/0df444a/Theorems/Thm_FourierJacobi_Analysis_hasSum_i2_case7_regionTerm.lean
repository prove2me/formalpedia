-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case7_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i2_case7_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:21.562265+00:00
-- url     : https://prove2.me/theorems/a8005ff3-fa27-4470-9ec5-ec6f173f6ce5
-- title:
--   Analysis: has Sum i2 case7 region Term
-- statement:
--   The Analysis construction uses the has Sum i2 case7 region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1219-L1244
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L1219-L1244

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

theorem FourierJacobi.Analysis.hasSum_i2_case7_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 18 => i2SpatialTerm q t d U V T 18 p.val)
      (i2RegionTerm 18 t d (T * U) (T * V)) := by sorry
