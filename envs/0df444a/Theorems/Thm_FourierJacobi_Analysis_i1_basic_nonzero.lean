-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_basic_nonzero
-- name    : FourierJacobi.Analysis.i1_basic_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:28.297009+00:00
-- url     : https://prove2.me/theorems/91bba93e-fae8-4951-a608-48cb6077c43d
-- title:
--   Analysis: i1 basic nonzero
-- statement:
--   The Analysis construction uses the i1 basic nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1161-L1172
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1161-L1172

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

theorem FourierJacobi.Analysis.i1_basic_nonzero (q t : ℂ) (hqt : q*t^2=1) (hz : ‖t^2‖<1) :
    t ≠ 0 ∧ q ≠ 0 ∧ q-1 ≠ 0 := by sorry
