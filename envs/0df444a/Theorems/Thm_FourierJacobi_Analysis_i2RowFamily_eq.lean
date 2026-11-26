-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2RowFamily_eq
-- name    : FourierJacobi.Analysis.i2RowFamily_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:15.542495+00:00
-- url     : https://prove2.me/theorems/85fc4b79-6685-5caa-9c00-537ad31316f5
-- title:
--   Analysis: i2 Row Family eq
-- statement:
--   The Analysis construction uses the i2 Row Family eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L338-L348
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L338-L348

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.i2RowFamily_eq (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) :
    i2RowFamily q t d U V T ν p = i2BareTerm q t d U V T ν p.1 * i2DepthWeight q ν p.1 p.2 := by sorry
