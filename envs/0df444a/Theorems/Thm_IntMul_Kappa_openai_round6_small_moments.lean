-- Prove2me | Theorems.Thm_IntMul_Kappa_openai_round6_small_moments
-- name    : IntMul.Kappa.openai_round6_small_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:33:48.979512+00:00
-- url     : https://prove2.me/theorems/ce3c7e5f-1c97-4230-94a2-0a7f1ae88d40
-- title:
--   Certified round-six moments at conservative 10^-7 savings
-- statement:
--   The exact Jain round-six bit histogram has moment strictly below 148225616 at exponent 1−10^-7, and the exact complex histogram has moment strictly below 207387136 at that exponent. This is much weaker than Jain's near-optimal parameters, but enough for the tiny OpenAI saving 2^-182. Unlike a floating-point certificate, the proof uses an exact rational affine upper bound from weighted AM-GM and evaluates only finite rational sums; all histogram coefficients are frozen platform definitions.
-- source:
--   OpenAI integer multiplication below n log n, September 2026; Jain Round6 network histogram frozen at commit f2176bc, exact rational estimates by weighted AM-GM. Supports the parent theorem IntMul.Kappa.openai_theorem_1.

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
open IntMul.Kappa

theorem IntMul.Kappa.openai_round6_small_moments :
    histMoment Jain.bitR6 529 (1 - (1 : ℝ) / 10 ^ 7) < 148225616 ∧
    histMoment Jain.cxR6 576 (1 - (1 : ℝ) / 10 ^ 7) < 207387136 := by sorry
