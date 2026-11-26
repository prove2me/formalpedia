-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
-- name    : FourierJacobi.Analysis.i1r10DepthEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:35.814142+00:00
-- url     : https://prove2.me/theorems/4561703f-fbb6-4795-bb15-41e6dbbf08af
-- title:
--   Analysis: i1r10 Depth Equiv val
-- statement:
--   The Analysis construction uses the i1r10 Depth Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Partition.lean#L451-L452
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Partition.lean#L451-L452

import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Definitions.Def_FourierJacobi_Analysis_I1Partition
set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem FourierJacobi.Analysis.i1r10DepthEquiv_val (p : I1R10Row × ℕ) :
    (i1r10DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := by sorry

attribute [defeq] FourierJacobi.Analysis.i1r10DepthEquiv_val
