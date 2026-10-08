-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_conditional_liouvilleLogSaving
-- name    : OAI.TwoPointCorrelations.conditional_liouvilleLogSaving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:39.852035+00:00
-- url     : https://prove2.me/theorems/54e09c7d-c2ff-4513-9eb7-313d374ed75e
-- title:
--   Ordinary affine Liouville correlations save a power of log, conditional on four analytic inputs
-- statement:
--   Assume `ModFiveThetaInput`, `BravermanDepth22Input`, `PrimeReciprocalInput` (see the bundle; respectively the mod-5 prime number theorem with de la Vallée Poussin error, Braverman's depth-22 AC⁰ theorem, and $|\sum_{p\le y}1/p-\log\log y|\le C$ for $y\ge2$) and `MRTLiouvilleShortInput` (there is $C>0$ such that for all naturals $10\le H\le X$ and real $\alpha$, the short exponential integral of the Liouville function `shortExponentialIntegral liouville X H α` is at most $C\,H\,X\cdot$`mrtShortError X H`). Then `LiouvilleLogSaving` holds: there is $c>0$ such that for all naturals $a_1,a_2>0$ and $b_1,b_2$ with $a_1b_2\ne a_2b_1$ there is $C>0$ with
--
--   $$\Big|\sum_{n=1}^{\lfloor X\rfloor}\lambda(a_1n+b_1)\lambda(a_2n+b_2)\Big|\le\frac{C\,X}{(\log X)^c}\qquad(X\ge3),$$
--
--   $\lambda$ being the Liouville function.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.conditional_liouvilleLogSaving`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter

theorem conditional_liouvilleLogSaving (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) : LiouvilleLogSaving := by
  sorry

end OAI.TwoPointCorrelations
