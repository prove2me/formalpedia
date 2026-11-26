-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case4_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case4_regionTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:00:20.547552+00:00
-- url     : https://prove2.me/theorems/0bab7f0d-c891-572d-8c5a-efd92d780002
-- title:
--   Analysis: has Sum i0 case4 region Term
-- statement:
--   The Analysis construction uses the has Sum i0 case4 region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L397-L410
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L397-L410

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem FourierJacobi.Analysis.hasSum_i0_case4_regionTerm (t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 3) := by sorry
