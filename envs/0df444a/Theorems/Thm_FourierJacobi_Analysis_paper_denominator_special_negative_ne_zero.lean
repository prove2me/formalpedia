-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paper_denominator_special_negative_ne_zero
-- name    : FourierJacobi.Analysis.paper_denominator_special_negative_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:38.971799+00:00
-- url     : https://prove2.me/theorems/b8d07710-64c0-4580-bd2c-c0aabbcac803
-- title:
--   Analysis: paper denominator special negative ne zero
-- statement:
--   The Analysis construction uses the paper denominator special negative ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L107-L125
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L107-L125

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paper_denominator_special_negative_ne_zero (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ -1) (hb₁ : b ≠ -1) :
    paperC q * paperD1 q a b (-(inverseSqrt q : ℂ)) *
      paperD2 q a b (-(inverseSqrt q : ℂ)) ≠ 0 := by sorry
