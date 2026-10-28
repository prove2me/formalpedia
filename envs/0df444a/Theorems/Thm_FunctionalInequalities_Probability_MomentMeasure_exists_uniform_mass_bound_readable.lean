-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_mass_bound_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:06.833414+00:00
-- url     : https://prove2.me/theorems/c940a54c-60e4-4d0d-a533-f6c9ae3a6309
-- title:
--   Polynomial Bound On Legendre Mass
-- statement:
--   This is a uniform polynomial bound for conjugate mass in the coercivity argument.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $dx$ be an additive Haar measure and let $\mu$ be a finite measure. Assume that $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $A>0$ such that every $\phi:E\to\overline{\mathbb R}$ with
--
--   1. $\phi\ge0$;
--   2. $\phi(0)=0$;
--   3. `ConvexPotential φ`;
--   4. `PotentialIntegrable φ μ`;
--
--   satisfies
--   $$\operatorname{mass}(dx,\phi^*)\le\operatorname{ENNReal.ofReal}\!\left(A\left(\max\left\{\int_E\phi(x).\operatorname{toReal}\,d\mu(x),1\right\}\right)^{\dim E}\right).$$
--
--   The constant is selected before $\phi$, and the estimate is polynomial in the maximum of the real integral and $1$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_uniform_mass_bound (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
--       (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
--       ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
--         (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
--         mass dx (legendre φ) ≤ ENNReal.ofReal
--           (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`density_scaled_le_exp`](https://prove2.me/theorems/19c43856-85c8-4cf6-9dbe-f234f3ec52f0), [`exists_uniform_legendre_lower`](https://prove2.me/theorems/a15b2ea9-f03f-4130-82da-67d156766d05), [`integrable_exp_sub_norm`](https://prove2.me/theorems/6e84bf56-c441-4d85-881f-7cdd5b15ecb5).
--
--   Previous: [`density_scaled_le_exp`](https://prove2.me/theorems/19c43856-85c8-4cf6-9dbe-f234f3ec52f0) · Next: [`exists_coercivity_of_centered_probability`](https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2).
--
--   [Source excerpt, lines 137–142](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L137-L142) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L134-L168 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

open FunctionalInequalities.Analysis
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_readable (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      mass dx (legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E) := by sorry
