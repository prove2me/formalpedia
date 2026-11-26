-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2Classify_mem
-- name    : FourierJacobi.Analysis.i2Classify_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:07:23.372065+00:00
-- url     : https://prove2.me/theorems/11df9bec-6f98-5d4e-bfbc-ff62ba37f267
-- title:
--   Analysis: i2 Classify mem
-- statement:
--   The Analysis construction uses the i2 Classify mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Partition.lean#L36-L40
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Partition.lean#L36-L40

import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Partition
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem FourierJacobi.Analysis.i2Classify_mem (k j h : ℤ) (c : ℕ) :
    i2SpatialPredicate (i2Classify k j h c) (k,j,h) ∧
      i2DepthPredicate (i2Classify k j h c) c := by sorry
