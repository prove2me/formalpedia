-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r4_master
-- name    : FourierJacobi.Analysis.summable_norm_i1r4_master
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:08.500228+00:00
-- url     : https://prove2.me/theorems/9600cf48-415c-55e8-804c-bff81ae03a7a
-- title:
--   Analysis: summable norm i1r4 master
-- statement:
--   The Analysis construction uses the summable norm i1r4 master property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L403-L412
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L403-L412

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

theorem FourierJacobi.Analysis.summable_norm_i1r4_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 6 => ‖masterTerm q t d U V T 1 p.val‖) := by sorry
