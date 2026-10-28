-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_uniform_functional_upper_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:00.848169+00:00
-- url     : https://prove2.me/theorems/10adc7a4-9c9b-442c-bc6e-416017b43c78
-- title:
--   Uniform Upper Bound For Admissible CEK Competitors
-- statement:
--   This is the finite-range reduction statement from the proof of Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), although no paper item directly cites this declaration.
--
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace with full $\mu$-measure equals $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Then there exists $U\in\mathbb R$ such that every $f:E\to\overline{\mathbb R}$ with `PotentialIntegrable f μ` satisfies
--   $$\operatorname{variationalFunctional}(dx,\mu,f)\le(U:\overline{\mathbb R}).$$
--
--   No convexity, nonnegativity, normalization, or finiteness of the conjugate mass is required of the competitor beyond `PotentialIntegrable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_uniform_functional_upper (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       ∃ U : ℝ, ∀ f : E → EReal, PotentialIntegrable f μ →
--         variationalFunctional dx μ f ≤ (U : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/Competitors`](https://prove2.me/theorems/410b5025-3a6c-4242-b99c-d26173c8306c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Supporting theorems: [`exists_normalized_competitor`](https://prove2.me/theorems/7f87c5ef-b945-49cc-bffa-16b93706462f), [`exists_coercivity_of_centered_probability`](https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2), [`real_coercivity_le_uniform`](https://prove2.me/theorems/4b9111c6-9576-4b77-b712-57c19eb68875).
--
--   Previous: [`exists_normalized_competitor`](https://prove2.me/theorems/7f87c5ef-b945-49cc-bffa-16b93706462f).
--
--   [Source excerpt, lines 58–62](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L58-L62) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L55-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.Competitors`, declaration `FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_Competitors

open FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_readable (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ U : ℝ, ∀ f : E → EReal, PotentialIntegrable f μ →
      variationalFunctional dx μ f ≤ (U : EReal) := by sorry
