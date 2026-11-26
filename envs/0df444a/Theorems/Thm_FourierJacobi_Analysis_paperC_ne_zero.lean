-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperC_ne_zero
-- name    : FourierJacobi.Analysis.paperC_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:36.753872+00:00
-- url     : https://prove2.me/theorems/da0888aa-34eb-4b9b-8991-7fe23f4ec2b8
-- title:
--   Analysis: paper C ne zero
-- statement:
--   The Analysis construction uses the paper C ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L32-L34
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L32-L34

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperC_ne_zero (q : ℝ) (hq : 1 < q) : paperC q ≠ 0 := by sorry
