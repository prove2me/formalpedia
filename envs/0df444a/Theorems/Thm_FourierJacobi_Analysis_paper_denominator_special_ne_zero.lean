-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paper_denominator_special_ne_zero
-- name    : FourierJacobi.Analysis.paper_denominator_special_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:38:46.30969+00:00
-- url     : https://prove2.me/theorems/e0215e71-276f-4825-8391-bb69277c736b
-- title:
--   Analysis: paper denominator special ne zero
-- statement:
--   Both literal special denominators are justified from precisely the endpoint
--   exclusions a,b ≠ ε, where ε is a sign. This asserts no endpoint series convergence.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L129-L138
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L129-L138

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.paper_denominator_special_ne_zero (q : ℝ) (hq : 1 < q)
    (a b ε : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hε : ε = 1 ∨ ε = -1) (haε : a ≠ ε) (hbε : b ≠ ε) :
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 := by sorry
