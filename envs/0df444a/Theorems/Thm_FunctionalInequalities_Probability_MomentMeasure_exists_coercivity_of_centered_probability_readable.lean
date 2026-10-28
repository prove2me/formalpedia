-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_coercivity_of_centered_probability_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:58.500131+00:00
-- url     : https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2
-- title:
--   Coercivity From Centering And Full-Dimensional Support
-- statement:
--   This formalizes the coercivity support associated with Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as a stronger related statement.
--
--   Let $E$ be finite-dimensional with a real inner product, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace carrying full $\mu$-measure is all of $E$:
--      $$\mu(V^c)=0\implies V=E.$$
--   2. The identity map $x\mapsto x$ is $\mu$-integrable.
--   3. The barycenter is zero:
--      $$\int_E x\,d\mu(x)=0.$$
--
--   Then there exists $A>0$ such that every nonnegative `ConvexPotential` $\phi$ with $\phi(0)=0$ and `PotentialIntegrable φ μ` satisfies both
--   $$\operatorname{mass}(dx,\phi^*)\le\operatorname{ENNReal.ofReal}\!\left(A\left(\max\left\{\int\phi.\operatorname{toReal}\,d\mu,1\right\}\right)^{\dim E}\right)$$
--   and
--   $$\operatorname{variationalFunctional}(dx,\mu,\phi)\le\left(\log A+\dim(E)\log\max\left\{\int\phi.\operatorname{toReal}\,d\mu,1\right\}-\int\phi.\operatorname{toReal}\,d\mu\right).$$
--
--   This is a uniform coercivity estimate, not an existence theorem for a maximizer or a claim about a particular numerical constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_coercivity_of_centered_probability (dx μ : Measure E)
--       [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
--         (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
--         (mass dx (legendre φ) ≤ ENNReal.ofReal
--           (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) ∧
--         variationalFunctional dx μ φ ≤
--           ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
--             (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`exists_uniform_mass_bound`](https://prove2.me/theorems/c940a54c-60e4-4d0d-a533-f6c9ae3a6309), [`zero_mem_interior_convexHull_support_of_integral_eq_zero`](https://prove2.me/theorems/24d566b9-c33c-4ef2-a315-a7ad900693e2).
--
--   Previous: [`exists_uniform_mass_bound`](https://prove2.me/theorems/c940a54c-60e4-4d0d-a533-f6c9ae3a6309) · Next: [`exists_bound_of_log_lower`](https://prove2.me/theorems/98239541-fa41-45b3-93db-26285bcefb48).
--
--   [Source excerpt, lines 188–198](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L188-L198) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L185-L209 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

open FunctionalInequalities.Analysis
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_readable (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      (mass dx (legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) ∧
      variationalFunctional dx μ φ ≤
        ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
          (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) := by sorry
