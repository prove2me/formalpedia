-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_modFive_normalized_logderiv_norm
-- name    : OAI.TwoPointCorrelations.modFive_normalized_logderiv_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:25.542201+00:00
-- url     : https://prove2.me/theorems/60e6c5e9-e0a5-4476-9dae-c4a732194a84
-- title:
--   Logarithmic-derivative bound for a normalized mod-5 L-function away from its zeros
-- statement:
--   Let $\chi$ be a nonprincipal Dirichlet character modulo $5$, $t$ real, and $\Lambda_t(z)=L(2+it+\frac32z,\chi)/L(2+it,\chi)$ (`modFiveNormalizedLFunction χ t`). Let $|z|\le3/4$ with $\Lambda_t(z)\ne0$, and $\eta>0$ such that $|z-\rho|\ge\eta$ for every zero $\rho$ of $\Lambda_t$ in the closed disc $|\rho|\le7/8$ (`modFiveNormalizedZeros χ t`). Then
--
--   $$\Big|\frac{\Lambda_t'(z)}{\Lambda_t(z)}\Big|\le\Big(c_L+\frac{1}{\eta\log\frac{15/16}{7/8}}\Big)\log\big(8c_I(|t|+4)\big),$$
--
--   with the explicit constants $c_L$ = `modFiveLogDerivativeConstant` $=\frac{16(4/5)^2}{(4/5-3/4)^3}+\Big(\big(\tfrac{(15/16)^2}{7/8}-\tfrac78\big)\log\tfrac{15/16}{7/8}\Big)^{-1}$ and $c_I$ = `modFiveInverseConstant` $=1+\sum_{n}|n^{-2}|$ (Mathlib's `LSeries.term 1 2`, which is $0$ at $n=0$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.modFive_normalized_logderiv_norm`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped BigOperators
open scoped Classical
open scoped Topology

theorem modFive_normalized_logderiv_norm (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : modFiveNormalizedLFunction χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ modFiveNormalizedZeros χ t, η ≤ ‖z - ρ‖) :
    ‖deriv (modFiveNormalizedLFunction χ t) z / modFiveNormalizedLFunction χ t z‖ ≤
      (modFiveLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) *
          Real.log (8 * modFiveInverseConstant * (|t| + 4)) := by
  sorry

end OAI.TwoPointCorrelations
