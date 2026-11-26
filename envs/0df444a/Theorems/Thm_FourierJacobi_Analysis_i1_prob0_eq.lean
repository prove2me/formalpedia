-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_prob0_eq
-- name    : FourierJacobi.Analysis.i1_prob0_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:52.235515+00:00
-- url     : https://prove2.me/theorems/7b9a2617-d04a-59f6-885b-f783414796e3
-- title:
--   Analysis: i1 prob0 eq
-- statement:
--   The Analysis construction uses the i1 prob0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L24-L31
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L24-L31

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

theorem FourierJacobi.Analysis.i1_prob0_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q*t^2=1)
    (hz : 1-t^2 ≠ 0) : collisionProbability q 0 = (1-2*t^2)/(1-t^2) := by sorry
