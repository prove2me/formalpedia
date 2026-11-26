-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row0
-- name    : FourierJacobi.Analysis.i2RegionTerm_row0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:29:18.182598+00:00
-- url     : https://prove2.me/theorems/81f53cf9-3dec-5a9d-ae2d-9672137647dd
-- title:
--   Analysis: i2 Region Term row0
-- statement:
--   The Analysis construction uses the i2 Region Term row0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L74-L77
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean#L74-L77

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

theorem FourierJacobi.Analysis.i2RegionTerm_row0 (t d U V : ℂ) :
    i2RegionTerm 0 t d U V = Algebra.regionTerm25 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := by sorry

attribute [defeq] FourierJacobi.Analysis.i2RegionTerm_row0
