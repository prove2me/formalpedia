-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paper_denominator_interior_ne_zero
-- name    : FourierJacobi.Analysis.paper_denominator_interior_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:57.629017+00:00
-- url     : https://prove2.me/theorems/df413ddf-ba7a-4d0f-9c23-665a5fdb2138
-- title:
--   Analysis: paper denominator interior ne zero
-- statement:
--   In the open interior, the actual denominator is nonzero even on Weyl walls.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L61-L68
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L61-L68

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paper_denominator_interior_ne_zero (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : inverseSqrt q < ‖d‖) (hdhi : ‖d‖ ≤ 1) :
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 := by sorry
