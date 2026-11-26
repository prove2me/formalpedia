-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r3c_master_reindexed
-- name    : FourierJacobi.Analysis.i1r3c_master_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:50.557917+00:00
-- url     : https://prove2.me/theorems/2d9c95a9-e314-50a4-baf5-3c42d7b1224b
-- title:
--   Analysis: i1r3c master reindexed
-- statement:
--   The Analysis construction uses the i1r3c master reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L318-L332
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L318-L332

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

theorem FourierJacobi.Analysis.i1r3c_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r3cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by sorry
