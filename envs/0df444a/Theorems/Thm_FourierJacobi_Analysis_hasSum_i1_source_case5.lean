-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_source_case5
-- name    : FourierJacobi.Analysis.hasSum_i1_source_case5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:40:48.959952+00:00
-- url     : https://prove2.me/theorems/21338862-9e7d-4932-91f0-9af9b65fef9e
-- title:
--   Analysis: has Sum i1 source case5
-- statement:
--   The Analysis construction uses the has Sum i1 source case5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1SourceRows.lean#L73-L80
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1SourceRows.lean#L73-L80

import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I1SourceRows
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false

theorem FourierJacobi.Analysis.hasSum_i1_source_case5 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 7 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 16) := by sorry
