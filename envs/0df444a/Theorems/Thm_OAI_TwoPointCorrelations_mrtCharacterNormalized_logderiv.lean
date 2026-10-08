-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrtCharacterNormalized_logderiv
-- name    : OAI.TwoPointCorrelations.mrtCharacterNormalized_logderiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:13.60734+00:00
-- url     : https://prove2.me/theorems/28b777af-4dd8-4dd9-a580-0e52941cea88
-- title:
--   Partial-fraction approximation of the logarithmic derivative of the normalized L-function
-- statement:
--   Let $q\ne0$, $\chi$ a nonprincipal character modulo $q$, $t$ real, and $\Lambda(z)=L(2+it+\frac32z,\chi)/L(2+it,\chi)$ (`mrtCharacterNormalizedLFunction χ t`). Let $Z$ be the (finite, by `mrtCharacterNormalizedZeros_finite`) set of zeros of $\Lambda$ in the closed disc $|\rho|\le7/8$. Then for every $z$ with $|z|\le3/4$ and $\Lambda(z)\ne0$,
--
--   $$\Big|\frac{\Lambda'(z)}{\Lambda(z)}-\sum_{\rho\in Z}\frac{m_\rho}{z-\rho}\Big|\le c_L\log\big(2q\,c_I(|t|+4)\big),$$
--
--   where $m_\rho$ is the order of vanishing of $\Lambda$ at $\rho$, $c_L$ = `mrtCharacterLogDerivativeConstant` $=\frac{16(4/5)^2}{(4/5-3/4)^3}+\Big(\big(\tfrac{(15/16)^2}{7/8}-\tfrac78\big)\log\tfrac{15/16}{7/8}\Big)^{-1}$ and $c_I$ = `mrtCharacterInverseConstant` $=1+\sum_{n\ge1}n^{-2}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrtCharacterNormalized_logderiv`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped BigOperators
open scoped Classical
open scoped Topology
variable {q : ℕ} [NeZero q]

theorem mrtCharacterNormalized_logderiv (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : mrtCharacterNormalizedLFunction χ t z ≠ 0) :
    ‖deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z -
      ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
        (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat / (z - ρ)‖ ≤
      mrtCharacterLogDerivativeConstant *
        Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  sorry

end OAI.TwoPointCorrelations
