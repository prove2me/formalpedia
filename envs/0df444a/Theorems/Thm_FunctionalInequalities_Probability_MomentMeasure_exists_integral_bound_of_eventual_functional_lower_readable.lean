-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integral_bound_of_eventual_functional_lower_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:03.102077+00:00
-- url     : https://prove2.me/theorems/ec1ab899-a2cd-4af7-a22e-cf39c5c47111
-- title:
--   Integral Bounds From An Eventual Functional Lower Bound
-- statement:
--   This is the normalized-sequence integral-control statement corresponding to estimate (62) in the coercivity framework.
--
--   Let $E$ be finite-dimensional with additive Haar measure $dx$, and let $\mu$ be a probability measure satisfying:
--
--   1. Every linear subspace with full $\mu$-measure equals $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Let $\phi_j:E\to\overline{\mathbb R}$ be a sequence such that every $\phi_j\ge0$, $\phi_j(0)=0$, `ConvexPotential (φ j)`, and `PotentialIntegrable (φ j) μ`. If, for some $b\in\mathbb R$, eventually in $j$,
--   $$b\le\operatorname{variationalFunctional}(dx,\mu,\phi_j),$$
--   then there exists $B\ge0$ such that
--   $$\int_E(\phi_j(x)).\operatorname{toReal}\,d\mu(x)\le B\quad\text{for every }j,$$
--   and
--   $$\sup_j\int^-_E(\phi_j(x)).\operatorname{toENNReal}\,d\mu(x)\ne+\infty.$$
--
--   The bound includes the finite initial segment of the sequence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_integral_bound_of_eventual_functional_lower
--       (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
--       (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
--       (hconv : ∀ j, ConvexPotential (φ j)) (hφ : ∀ j, PotentialIntegrable (φ j) μ)
--       (b : ℝ) (hlower : ∀ᶠ j in atTop, (b : EReal) ≤ variationalFunctional dx μ (φ j)) :
--       ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
--         (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`exists_bound_of_log_lower`](https://prove2.me/theorems/98239541-fa41-45b3-93db-26285bcefb48), [`exists_coercivity_of_centered_probability`](https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2).
--
--   Previous: [`exists_bound_of_log_lower`](https://prove2.me/theorems/98239541-fa41-45b3-93db-26285bcefb48) · Next: [`real_coercivity_le_uniform`](https://prove2.me/theorems/4b9111c6-9576-4b77-b712-57c19eb68875).
--
--   [Source excerpt, lines 246–254](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L246-L254) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L243-L270 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

open FunctionalInequalities.Analysis
open MeasureTheory Filter Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower_readable
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
    (hconv : ∀ j, ConvexPotential (φ j)) (hφ : ∀ j, PotentialIntegrable (φ j) μ)
    (b : ℝ) (hlower : ∀ᶠ j in atTop, (b : EReal) ≤ variationalFunctional dx μ (φ j)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
      (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by sorry
