-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_lemma_C_1
-- name    : HighDimCLT.Hyperrect.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:33.302053+00:00
-- url     : https://prove2.me/theorems/b6789846-2e94-40b7-b072-533e9b8e95bd
-- title:
--   Lemma C.1, p. 2332 — P(ξ > x) ≤ Ae^{−x/B} ⇒ E[ξ³1{ξ > t}] ≤ 6A(t + B)³e^{−t/B}
-- statement:
--   Let $\xi$ be a nonnegative random variable and let $A, B > 0$ be constants such that
--
--   $$\mathrm P(\xi > x) \le A e^{-x/B} \quad\text{for all } x \ge 0.$$
--
--   Then for every $t \ge 0$,
--
--   $$\mathrm E\big[\xi^3 1\{\xi > t\}\big] \le 6A(t + B)^3 e^{-t/B}.$$
--
--   This converts an exponential tail bound into a bound on a truncated third moment; it is how the quantity $M_n(\phi_n)$ of Theorem 2.1 is estimated in the proof of Proposition 2.1.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0, \infty]$, so the conclusion also asserts that it is finite. Nonnegativity of $\xi$ is required almost surely.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2332, App. C, Lemma C.1

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

theorem lemma_C_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (hξm : Measurable ξ) (hξ0 : ∀ᵐ ω ∂P, 0 ≤ ξ ω)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (htail : ∀ x : ℝ, 0 ≤ x → P.real {ω | x < ξ ω} ≤ A * Real.exp (-x / B))
    (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (if t < ξ ω then ξ ω ^ 3 else 0) ∂P
      ≤ ENNReal.ofReal (6 * A * (t + B) ^ 3 * Real.exp (-t / B)) := by sorry

end HighDimCLT.Hyperrect
