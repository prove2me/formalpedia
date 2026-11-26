-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r8ao_master_reindexed
-- name    : FourierJacobi.Analysis.i1r8ao_master_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:57.525675+00:00
-- url     : https://prove2.me/theorems/2fe65591-5693-423c-9136-65046350ce75
-- title:
--   Analysis: i1r8ao master reindexed
-- statement:
--   The Analysis construction uses the i1r8ao master reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L705-L717
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L705-L717

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

theorem FourierJacobi.Analysis.i1r8ao_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r8aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by sorry
