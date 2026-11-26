-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r4_cartan
-- name    : FourierJacobi.Analysis.i1r4_cartan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:39.709797+00:00
-- url     : https://prove2.me/theorems/0cda3be0-dc3b-4a2e-a11c-dfeaaae1cebf
-- title:
--   Analysis: i1r4 cartan
-- statement:
--   The Analysis construction uses the i1r4 cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L590-L597
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L590-L597

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

theorem FourierJacobi.Analysis.i1r4_cartan (p : I1R4Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by sorry
