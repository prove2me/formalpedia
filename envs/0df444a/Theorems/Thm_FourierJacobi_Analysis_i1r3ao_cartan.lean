-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r3ao_cartan
-- name    : FourierJacobi.Analysis.i1r3ao_cartan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:09.776268+00:00
-- url     : https://prove2.me/theorems/6b901e11-71eb-4c6d-bdec-329b50965479
-- title:
--   Analysis: i1r3ao cartan
-- statement:
--   The Analysis construction uses the i1r3ao cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L342-L352
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L342-L352

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem FourierJacobi.Analysis.i1r3ao_cartan (p : I1R3AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by sorry
