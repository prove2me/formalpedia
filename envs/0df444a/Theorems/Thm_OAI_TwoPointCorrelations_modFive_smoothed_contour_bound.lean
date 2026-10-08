-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_modFive_smoothed_contour_bound
-- name    : OAI.TwoPointCorrelations.modFive_smoothed_contour_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:06.473998+00:00
-- url     : https://prove2.me/theorems/b5d05653-fda3-4f22-a236-9b95fb851859
-- title:
--   A Perron contour bound for the Cesàro-smoothed twisted Chebyshev sum modulo 5
-- statement:
--   There are $a\in(0,1/4]$, $C>0$ and $D>0$ such that for every nonprincipal Dirichlet character $\chi$ modulo $5$ and all reals $T\ge2$, $x\ge1$ not an integer, $\delta\in(0,1]$,
--
--   $$\big|\psi_\chi(x)\big|\le4\pi C\log^2(T+2)\,x^{1-a/\log(T+2)}+\frac{4C\log^2(T+2)\,x^{1+\delta}}{T^2}+\frac{2(1/\delta+D)\,x^{1+\delta}}T,$$
--
--   where $\psi_\chi(x)$ = `modFiveSmoothedPsi χ x` $=\sum_{1\le n\le x}\Lambda_\chi(n)(1-n/x)$, with $\Lambda_\chi$ = `modFiveMangoldtTwist χ` the bundle's twisted von Mangoldt function.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.modFive_smoothed_contour_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open _root_.Erdos970

theorem modFive_smoothed_contour_bound : ∃ a C D : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧ 0 < D ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T x δ : ℝ,
      2 ≤ T → 1 ≤ x → 0 < δ → δ ≤ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ x‖ ≤
        4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
          4 * C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2 +
          2 * (1 / δ + D) * x ^ (1 + δ) / T := by
  sorry

end OAI.TwoPointCorrelations
