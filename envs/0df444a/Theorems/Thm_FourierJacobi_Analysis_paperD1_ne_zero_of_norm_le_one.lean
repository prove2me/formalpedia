-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperD1_ne_zero_of_norm_le_one
-- name    : FourierJacobi.Analysis.paperD1_ne_zero_of_norm_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:39.825915+00:00
-- url     : https://prove2.me/theorems/8341ad3f-f57f-463a-a963-68e340296e0a
-- title:
--   Analysis: paper D1 ne zero of norm le one
-- statement:
--   The Analysis construction uses the paper D1 ne zero of norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L36-L46
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L36-L46

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperD1_ne_zero_of_norm_le_one (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ ≤ 1) :
    paperD1 q a b d ≠ 0 := by sorry
