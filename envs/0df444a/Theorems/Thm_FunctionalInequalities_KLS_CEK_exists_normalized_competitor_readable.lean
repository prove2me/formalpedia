-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_competitor_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_normalized_competitor_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:50.561518+00:00
-- url     : https://prove2.me/theorems/7f87c5ef-b945-49cc-bffa-16b93706462f
-- title:
--   Existence of an Epsilon-Normalized Convex Competitor
-- statement:
--   This formalizes the reduction step in the proof of Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $dx$ be an additive Haar measure and let $\mu$ be a probability measure on a finite-dimensional real inner-product space. Assume:
--
--   1. $\mu$ is not concentrated on any proper linear subspace;
--   2. the identity map is $\mu$-integrable;
--   3. $\mu$ is centered, $\int x\,d\mu(x)=0$;
--   4. $f$ is potential-integrable;
--   5. $\varepsilon>0$.
--
--   Then there exists $\psi:E\to\overline{\mathbb R}$ such that $\psi$ is a convex potential, is potential-integrable, and
--
--   $$
--   \psi(x)\geq0,\qquad \psi(0)=0,
--   $$
--
--   and its variational value satisfies
--
--   $$
--   \mathcal V_{dx,\mu}(f)
--   \leq
--   \mathcal V_{dx,\mu}(\psi)+\varepsilon.
--   $$
--
--   This provides an epsilon-close normalized convex competitor for variational arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_normalized_competitor (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
--       (f : E → EReal) (hf : PotentialIntegrable f μ) (ε : ℝ) (hε : 0 < ε) :
--       ∃ ψ : E → EReal, ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
--         (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
--         variationalFunctional dx μ f ≤ variationalFunctional dx μ ψ + (ε : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/Competitors`](https://prove2.me/theorems/410b5025-3a6c-4242-b99c-d26173c8306c).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Selected supporting theorems: [`exists_nonnegative_origin_zero_affine`](https://prove2.me/theorems/23dc8e13-df9f-4967-b282-729c3b46dcf2), [`legendre_affineSubtract`](https://prove2.me/theorems/86cc89dc-153b-4ec4-a574-1e72902d9a9b), [`affineSubtract_potentialIntegrable`](https://prove2.me/theorems/f9035aa8-a93c-47ed-80fb-13efe5d1963a), [`exists_convexified_lowerTruncate_variational_le_add`](https://prove2.me/theorems/0380bc20-68ac-4f5a-8497-6a23fbd646e5), [`integral_affineSubtract`](https://prove2.me/theorems/b464f0e5-346a-4249-bc07-ab1613a70aef).
--
--   Next: [`exists_uniform_functional_upper`](https://prove2.me/theorems/10adc7a4-9c9b-442c-bc6e-416017b43c78).
--
--   [Source excerpt, lines 32–38](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L32-L38) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L29-L54 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.Competitors`, declaration `FunctionalInequalities.KLS.CEK.exists_normalized_competitor`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_Competitors

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_normalized_competitor_readable (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (f : E → EReal) (hf : PotentialIntegrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : E → EReal, ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      variationalFunctional dx μ f ≤ variationalFunctional dx μ ψ + (ε : EReal) := by sorry
