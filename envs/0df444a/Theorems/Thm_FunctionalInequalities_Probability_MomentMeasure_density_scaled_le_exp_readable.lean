-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_density_scaled_le_exp_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.313267+00:00
-- url     : https://prove2.me/theorems/19c43856-85c8-4cf6-9dbe-f234f3ec52f0
-- title:
--   Scaled Legendre Density Exponential Bound
-- statement:
--   This is a technical density estimate for a nonnegative extended-real Legendre transform.
--
--   Let $E$ be a real inner-product normed additive group, let $\phi:E\to\overline{\mathbb R}$, and let $c,C,M,a\in\mathbb R$. Assume:
--
--   1. $0\le C$.
--   2. $1\le a$ and $M\le a$.
--   3. For every $y\in E$, the Legendre transform $\phi^*(y)$ is nonnegative and satisfies
--      $$c\|y\|-CM\le \phi^*(y).$$
--
--   Then, for every $y\in E$, the density associated with `density` and the scaled point $ay$ obeys
--   $$\operatorname{density}(\phi^*)(ay)\le \operatorname{ENNReal.ofReal}\!\left(\exp(C-c\|y\|)\right).$$
--
--   This provides a reusable exponential envelope after scaling, without finite-dimensionality or measurability assumptions in the statement.
--
--   **Formalization Note** The density and bound are $[0,\infty]$-valued (`ENNReal`); the exponent is an ordinary real number.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem density_scaled_le_exp (φ : E → EReal) {c C M a : ℝ}
--       (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
--       (hlower : ∀ y, 0 ≤ legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ legendre φ y)
--       (y : E) : density (legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`exists_uniform_legendre_lower`](https://prove2.me/theorems/a15b2ea9-f03f-4130-82da-67d156766d05) · Next: [`exists_uniform_mass_bound`](https://prove2.me/theorems/c940a54c-60e4-4d0d-a533-f6c9ae3a6309).
--
--   [Source excerpt, lines 103–106](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L103-L106) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L100-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_readable (φ : E → EReal) {c C M a : ℝ}
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
    (hlower : ∀ y, 0 ≤ legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ legendre φ y)
    (y : E) : density (legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖)) := by sorry
