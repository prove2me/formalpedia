-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_prob_tail
-- name    : FourierJacobi.Analysis.i1_summable_norm_prob_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:00.311037+00:00
-- url     : https://prove2.me/theorems/60fd3a0b-7bfd-4e37-8ec3-e099fadcb6e2
-- title:
--   Analysis: i1 summable norm prob tail
-- statement:
--   The Analysis construction uses the i1 summable norm prob tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L33-L36
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L33-L36

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

theorem FourierJacobi.Analysis.i1_summable_norm_prob_tail (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q (c+1)‖) := by sorry
