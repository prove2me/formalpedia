-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_hasSum_product
-- name    : FourierJacobi.Analysis.i1_hasSum_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:43.198822+00:00
-- url     : https://prove2.me/theorems/57f94f97-7bbb-4b23-a238-c0fd6e1b25ad
-- title:
--   Analysis: i1 has Sum product
-- statement:
--   The Analysis construction uses the i1 has Sum product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L38-L45
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L38-L45

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

theorem FourierJacobi.Analysis.i1_hasSum_product {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ)
    (s z : ℂ) (hf : HasSum f s) (hg : HasSum g z)
    (hfn : Summable (fun p => ‖f p‖)) (hgn : Summable (fun p => ‖g p‖)) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (s*z) := by sorry
