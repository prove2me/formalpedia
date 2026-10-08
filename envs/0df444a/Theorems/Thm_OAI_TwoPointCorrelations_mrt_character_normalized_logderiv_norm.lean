-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_character_normalized_logderiv_norm
-- name    : OAI.TwoPointCorrelations.mrt_character_normalized_logderiv_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:32.120976+00:00
-- url     : https://prove2.me/theorems/18488db9-84dd-41e5-a2aa-66871679d2cb
-- title:
--   Logarithmic-derivative bound for the normalized L-function at points away from its zeros
-- statement:
--   Let $q\ne0$, $\chi$ nonprincipal modulo $q$, $t$ real and $\Lambda(z)=L(2+it+\frac32z,\chi)/L(2+it,\chi)$. Let $|z|\le3/4$ with $\Lambda(z)\ne0$, and $\eta>0$ with $|z-\rho|\ge\eta$ for every zero $\rho$ of $\Lambda$ with $|\rho|\le7/8$ (`mrtCharacterNormalizedZeros χ t`). Then
--
--   $$\Big|\frac{\Lambda'(z)}{\Lambda(z)}\Big|\le\Big(c_L+\frac{1}{\eta\log\frac{15/16}{7/8}}\Big)\log\big(2q\,c_I(|t|+4)\big),$$
--
--   with $c_L$ = `mrtCharacterLogDerivativeConstant` and $c_I$ = `mrtCharacterInverseConstant` as in the bundle ($c_I=1+\sum_{n\ge1}n^{-2}$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_character_normalized_logderiv_norm`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped BigOperators
open scoped Classical
open scoped Topology
variable {q : ℕ} [NeZero q]

theorem mrt_character_normalized_logderiv_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : mrtCharacterNormalizedLFunction χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtCharacterNormalizedZeros χ t, η ≤ ‖z - ρ‖) :
    ‖deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z‖ ≤
      (mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  sorry

end OAI.TwoPointCorrelations
