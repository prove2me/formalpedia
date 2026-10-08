-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_character_logderiv_global_bound
-- name    : OAI.TwoPointCorrelations.mrt_character_logderiv_global_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:53.230576+00:00
-- url     : https://prove2.me/theorems/f0179322-79fb-478c-8447-2352ee6f420e
-- title:
--   A zero-free region and a bound for L′/L of nonprincipal characters to any modulus, uniform in q
-- statement:
--   There are $c>0$ and $C>0$ such that for every natural $q\ne0$, every nonprincipal Dirichlet character $\chi$ modulo $q$, and all reals $t,\sigma$ with $1-\frac{c}{q^2\,h_q(t)}\le\sigma\le2$, where $h_q(t)=\log(q(|t|+2))$ (`mrtCharacterHeight`):
--
--   $$L(\sigma+it,\chi)\ne0\qquad\text{and}\qquad\Big|\frac{L'(\sigma+it,\chi)}{L(\sigma+it,\chi)}\Big|\le C\,q^2\,h_q(t)^2,$$
--
--   with $L$ = Mathlib's `DirichletCharacter.LFunction χ` and $L'$ its complex derivative.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_character_logderiv_global_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_character_logderiv_global_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ t sigma : ℝ, 1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ sigma →
      sigma ≤ 2 →
      DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((sigma : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * (q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
