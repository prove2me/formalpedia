-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_modFiveThetaInput
-- name    : OAI.TwoPointCorrelations.modFiveThetaInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:57.9676+00:00
-- url     : https://prove2.me/theorems/db4fd294-1ddb-4f30-8c5a-0dd45451dd5d
-- title:
--   The prime number theorem with de la Vallée Poussin error term for the primes ≡ 1 and ≢ 1 modulo 5
-- statement:
--   `ModFiveThetaInput` holds: there are reals $c>0$ and $C\ge0$ such that for both choices of class and every real $x\ge2$,
--
--   $$\Big|\sum_{\substack{p\le x\\ p\equiv1\ (5)}}\log p-\frac x4\Big|\le Cx\,e^{-c\sqrt{\log x}},\qquad\Big|\sum_{\substack{p\le x\\ p\not\equiv1\ (5)}}\log p-\frac{3x}4\Big|\le Cx\,e^{-c\sqrt{\log x}},$$
--
--   the sums over primes $p\le\lfloor x\rfloor$ (`modFiveTheta`, `modFiveDensity`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.modFiveThetaInput`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset
open scoped BigOperators
open scoped Classical

theorem modFiveThetaInput : ModFiveThetaInput := by
  sorry

end OAI.TwoPointCorrelations
