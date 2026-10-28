-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_legendre_lower_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:01.880899+00:00
-- url     : https://prove2.me/theorems/a15b2ea9-f03f-4130-82da-67d156766d05
-- title:
--   Uniform Linear Lower Bound For Legendre Transforms
-- statement:
--   This is a coercivity-support statement for moment potentials.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure, and let $\mu$ be a finite measure. Assume that $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exist constants $c,C>0$ such that every $\phi:E\to\overline{\mathbb R}$ satisfying
--
--   1. $\phi\ge0$ pointwise;
--   2. $\phi(0)=0$;
--   3. `ConvexPotential φ`;
--   4. `PotentialIntegrable φ μ`;
--
--   has, for every $y\in E$,
--   $$0\le\phi^*(y)\quad\text{and}\quad c\|y\|-C\int_E\phi(x).\operatorname{toReal}\,d\mu(x)\le\phi^*(y).$$
--
--   The constants are chosen independently of the particular potential and provide a uniform linear lower bound for its Legendre transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_uniform_legendre_lower (μ : Measure E) [IsFiniteMeasure μ]
--       (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
--       ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ φ : E → EReal,
--         (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
--         ∀ y, 0 ≤ legendre φ y ∧
--           ((c * ‖y‖ - C * (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) ≤ legendre φ y
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Supporting theorems: [`affineMaximum_coercive`](https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70), [`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`](https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000).
--
--   Next: [`density_scaled_le_exp`](https://prove2.me/theorems/19c43856-85c8-4cf6-9dbe-f234f3ec52f0).
--
--   [Source excerpt, lines 53–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L53-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L50-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

open FunctionalInequalities.Analysis
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_readable (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      ∀ y, 0 ≤ legendre φ y ∧
        ((c * ‖y‖ - C * (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) ≤ legendre φ y := by sorry
