-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperD2_ne_zero_interior
-- name    : FourierJacobi.Analysis.paperD2_ne_zero_interior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:23.741018+00:00
-- url     : https://prove2.me/theorems/e58c7681-28e4-4ef9-a049-b9d3f2bcf200
-- title:
--   Analysis: paper D2 ne zero interior
-- statement:
--   The Analysis construction uses the paper D2 ne zero interior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L48-L58
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L48-L58

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paperD2_ne_zero_interior (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd : inverseSqrt q < ‖d‖) : paperD2 q a b d ≠ 0 := by sorry
