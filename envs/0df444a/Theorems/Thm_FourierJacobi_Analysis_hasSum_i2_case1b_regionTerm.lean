-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case1b_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i2_case1b_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:52.36943+00:00
-- url     : https://prove2.me/theorems/3ed1e350-e771-44f5-9030-510c924cd738
-- title:
--   Analysis: has Sum i2 case1b region Term
-- statement:
--   The Analysis construction uses the has Sum i2 case1b region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L325-L346
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L325-L346

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

theorem FourierJacobi.Analysis.hasSum_i2_case1b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 1 => i2SpatialTerm q t d U V T 1 p.val)
      (i2RegionTerm 1 t d (T * U) (T * V)) := by sorry
