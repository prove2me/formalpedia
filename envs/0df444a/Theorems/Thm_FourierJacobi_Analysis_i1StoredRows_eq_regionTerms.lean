-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1StoredRows_eq_regionTerms
-- name    : FourierJacobi.Analysis.i1StoredRows_eq_regionTerms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:05.308688+00:00
-- url     : https://prove2.me/theorems/c27b7585-2bc6-449b-8eb8-14d77b24173a
-- title:
--   Analysis: i1 Stored Rows eq region Terms
-- statement:
--   The Analysis construction uses the i1 Stored Rows eq region Terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1097-L1100
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1097-L1100

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.i1StoredRows_eq_regionTerms (t d U V T : ℂ) (i : Fin 15) :
    i1StoredRows t d U V T i =
      regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by sorry
