-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperD2_special_negative
-- name    : FourierJacobi.Analysis.paperD2_special_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:31.789392+00:00
-- url     : https://prove2.me/theorems/e7496ac9-9d32-42af-a07a-76d280a45478
-- title:
--   Analysis: paper D2 special negative
-- statement:
--   The Analysis construction uses the paper D2 special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L86-L92
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L86-L92

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperD2_special_negative (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    paperD2 q a b (-(inverseSqrt q : ℂ)) = satakeNumerator a b := by sorry
