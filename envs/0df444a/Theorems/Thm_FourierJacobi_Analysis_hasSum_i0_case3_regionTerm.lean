-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case3_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case3_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:25.529108+00:00
-- url     : https://prove2.me/theorems/e9f28099-069b-4883-8872-538c85878ff0
-- title:
--   Analysis: has Sum i0 case3 region Term
-- statement:
--   The Analysis construction uses the has Sum i0 case3 region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L382-L395
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L382-L395

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

theorem FourierJacobi.Analysis.hasSum_i0_case3_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 2) := by sorry
