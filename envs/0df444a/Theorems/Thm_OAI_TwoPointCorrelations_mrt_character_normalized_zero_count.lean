-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_character_normalized_zero_count
-- name    : OAI.TwoPointCorrelations.mrt_character_normalized_zero_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:05.198287+00:00
-- url     : https://prove2.me/theorems/9bb029a2-f950-4800-8760-ba631970683f
-- title:
--   The normalized L-function has at most log(2q c_I(|t|+4))/log(15/14) zeros in the disc of radius 7/8
-- statement:
--   Let $q\ne0$, $\chi$ a nonprincipal Dirichlet character modulo $q$, $t$ real, $\Lambda(z)=L(2+it+\frac32z,\chi)/L(2+it,\chi)$, and $Z$ the finite set of zeros of $\Lambda$ with $|\rho|\le7/8$. Then
--
--   $$\sum_{\rho\in Z}m_\rho\le\frac{1}{\log\frac{15/16}{7/8}}\,\log\big(2q\,c_I(|t|+4)\big),$$
--
--   with $m_\rho$ the order of vanishing at $\rho$ and $c_I$ = `mrtCharacterInverseConstant` $=1+\sum_{n\ge1}n^{-2}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_character_normalized_zero_count`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped BigOperators
open scoped Classical
open scoped Topology
variable {q : ℕ} [NeZero q]

theorem mrt_character_normalized_zero_count (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    (∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
      ((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℝ)) ≤
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  sorry

end OAI.TwoPointCorrelations
