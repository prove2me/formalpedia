-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_master_of_geometricRange
-- name    : FourierJacobi.Analysis.hasSum_i1_master_of_geometricRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:30.632535+00:00
-- url     : https://prove2.me/theorems/9b39c3b9-ba8c-5a7c-8220-0636bb3aa7aa
-- title:
--   Analysis: has Sum i1 master of geometric Range
-- statement:
--   All auxiliary nonzero q/t hypotheses follow from the independent
--   normalization equation and the convergent parameter range.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1176-L1181
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1176-L1181

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

theorem FourierJacobi.Analysis.hasSum_i1_master_of_geometricRange (q t d U V T : ℂ)
    (hd : d ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by sorry
