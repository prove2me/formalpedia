-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_eq_regionTerms
-- name    : FourierJacobi.Analysis.i2RegionTerm_eq_regionTerms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:00.229857+00:00
-- url     : https://prove2.me/theorems/ddc497ad-ebf0-54d1-9850-83578c32325b
-- title:
--   Analysis: i2 Region Term eq region Terms
-- statement:
--   The Analysis construction uses the i2 Region Term eq region Terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Ambient.lean#L18-L20
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Ambient.lean#L18-L20

import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Ambient
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

theorem FourierJacobi.Analysis.i2RegionTerm_eq_regionTerms (t d U V : ℂ) (ν : Fin 25) :
    i2RegionTerm ν t d U V = Algebra.regionTerms t d U V (i2Offset ν) := by sorry
