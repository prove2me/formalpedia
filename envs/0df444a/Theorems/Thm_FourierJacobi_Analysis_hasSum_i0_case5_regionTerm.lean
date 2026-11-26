-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case5_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case5_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:27.198803+00:00
-- url     : https://prove2.me/theorems/b69876e1-f8a2-5dc1-aca8-0bafa83c1211
-- title:
--   Analysis: has Sum i0 case5 region Term
-- statement:
--   The Analysis construction uses the has Sum i0 case5 region Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L412-L425
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L412-L425

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

theorem FourierJacobi.Analysis.hasSum_i0_case5_regionTerm (t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 4) := by sorry
