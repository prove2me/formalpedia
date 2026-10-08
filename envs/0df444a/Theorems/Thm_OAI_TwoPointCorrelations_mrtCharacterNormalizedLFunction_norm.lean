-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrtCharacterNormalizedLFunction_norm
-- name    : OAI.TwoPointCorrelations.mrtCharacterNormalizedLFunction_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:19.802289+00:00
-- url     : https://prove2.me/theorems/6d98ede3-9e0e-432e-bb0b-8e219173621a
-- title:
--   A polynomial bound for the normalized L-function L(2+it+3z/2,χ)/L(2+it,χ) on the unit disc
-- statement:
--   Let $q\ne0$ be natural, $\chi$ a nonprincipal Dirichlet character modulo $q$, $t$ real and $|z|\le1$. Then
--
--   $$\Big|\frac{L(2+it+\frac32z,\chi)}{L(2+it,\chi)}\Big|\le2q\,c_I\,(|t|+4),$$
--
--   where the left side is `mrtCharacterNormalizedLFunction χ t z` and $c_I$ = `mrtCharacterInverseConstant` $=1+\sum_{n\ge1}n^{-2}$ (as $1+\sum_n|$`LSeries.term 1 2 n`$|$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrtCharacterNormalizedLFunction_norm`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open ArithmeticFunction
open scoped BigOperators
open scoped Classical
open scoped LSeries.notation
open scoped ArithmeticFunction.Moebius
variable {q : ℕ} [NeZero q]

theorem mrtCharacterNormalizedLFunction_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖mrtCharacterNormalizedLFunction χ t z‖ ≤
      (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
  sorry

end OAI.TwoPointCorrelations
