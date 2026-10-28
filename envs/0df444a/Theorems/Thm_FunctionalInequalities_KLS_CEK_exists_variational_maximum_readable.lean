-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_variational_maximum_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_variational_maximum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:21.353386+00:00
-- url     : https://prove2.me/theorems/2658ff47-5952-426e-98f9-f3b3ec7e8d7b
-- title:
--   Existence of a Variational Maximizer
-- statement:
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. If a linear subspace $V\subseteq E$ satisfies $\mu(V^c)=0$, then $V=E$.
--   2. The identity map is integrable under $\mu$.
--   3. The barycenter is zero: $\int x\,d\mu=0$.
--
--   Then there exists $\phi:E\to\overline{\mathbb{R}}$ such that $\phi$ is a convex lower-semicontinuous potential, is potential-integrable under $\mu$, and
--
--   $$
--   \operatorname{mass}_{dx}(\phi^*)=1.
--   $$
--
--   For every potential-integrable competitor $f:E\to\overline{\mathbb{R}}$,
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(\phi),
--   $$
--
--   where $\phi^*$ is `legendre`, the mass is `mass`, and $I_{dx,\mu}$ is `variationalFunctional`. This is the formalized variational-attainment conclusion; it does not assert essential continuity, an Euler–Lagrange identity, or a moment-map formula.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_variational_maximum (dx μ : Measure E)
--       [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       ∃ φ : E → EReal, ConvexPotential φ ∧ LowerSemicontinuous φ ∧ PotentialIntegrable φ μ ∧
--         mass dx (legendre φ) = 1 ∧
--         ∀ f : E → EReal, PotentialIntegrable f μ →
--           variationalFunctional dx μ f ≤ variationalFunctional dx μ φ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/VariationalMaximum`](https://prove2.me/theorems/60547a65-c647-4027-80b6-d75ac35d269f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Selected supporting theorems: [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9), [`legendre_affineSubtract`](https://prove2.me/theorems/86cc89dc-153b-4ec4-a574-1e72902d9a9b), [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6), [`exists_limit_ge_normalized_supremum`](https://prove2.me/theorems/9ad1f752-005f-403f-b340-5ef5a45400a5), [`exists_normalized_competitor`](https://prove2.me/theorems/7f87c5ef-b945-49cc-bffa-16b93706462f).
--
--   Previous: [`exists_limit_ge_normalized_supremum`](https://prove2.me/theorems/9ad1f752-005f-403f-b340-5ef5a45400a5).
--
--   [Source excerpt, lines 138–145](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L138-L145) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Proposition 12, display (38), of Cordero–Klartag (arXiv:1304.0630v1).
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L134-L212 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_variational_maximum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_variational_maximum_readable (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal, ConvexPotential φ ∧ LowerSemicontinuous φ ∧ PotentialIntegrable φ μ ∧
      mass dx (legendre φ) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f μ →
        variationalFunctional dx μ f ≤ variationalFunctional dx μ φ := by sorry
