-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_maximizing_sequence_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:07.762689+00:00
-- url     : https://prove2.me/theorems/11706c73-d73a-45ce-a370-2f9ff07f3e79
-- title:
--   Normalized Maximizing Sequence For The Variational Functional
-- statement:
--   This formalizes a partial compactness consequence related to Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as a stronger paper statement.
--
--   Let $E$ be finite-dimensional with additive Haar measure $dx$, and let $\mu$ be a probability measure satisfying:
--
--   1. Every linear subspace with full $\mu$-measure is all of $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Then there exist $S\in\mathbb R$ and a sequence $\phi_j:E\to\overline{\mathbb R}$ such that, for every $j$, `ConvexPotential (φ j)`, `PotentialIntegrable (φ j) μ`, $\phi_j\ge0$, and $\phi_j(0)=0$. Moreover,
--   $$\operatorname{variationalFunctional}(dx,\mu,\phi_j)\longrightarrow(S:\overline{\mathbb R})$$
--   as $j\to\infty$, and every nonnegative normalized convex potential $\psi$ with `PotentialIntegrable ψ μ` satisfies
--   $$\operatorname{variationalFunctional}(dx,\mu,\psi)\le(S:\overline{\mathbb R}).$$
--
--   This provides a normalized maximizing sequence and an upper-bound value, but does not assert mass convergence or attainment by a single potential.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_normalized_maximizing_sequence (dx μ : Measure E)
--       [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       ∃ (S : ℝ) (φ : ℕ → E → EReal),
--         (∀ j, ConvexPotential (φ j)) ∧ (∀ j, PotentialIntegrable (φ j) μ) ∧
--         (∀ j x, 0 ≤ φ j x) ∧ (∀ j, φ j 0 = 0) ∧
--         Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 (S : EReal)) ∧
--         ∀ ψ : E → EReal, ConvexPotential ψ → PotentialIntegrable ψ μ →
--           (∀ x, 0 ≤ ψ x) → ψ 0 = 0 → variationalFunctional dx μ ψ ≤ (S : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/VariationalMaximum`](https://prove2.me/theorems/60547a65-c647-4027-80b6-d75ac35d269f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`legendre_norm`](https://prove2.me/theorems/7eb3b3f3-e05d-4ad0-a70e-b08de926b3ea), [`exists_uniform_functional_upper`](https://prove2.me/theorems/10adc7a4-9c9b-442c-bc6e-416017b43c78).
--
--   Next: [`exists_limit_ge_normalized_supremum`](https://prove2.me/theorems/9ad1f752-005f-403f-b340-5ef5a45400a5).
--
--   [Source excerpt, lines 35–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L35-L44) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L32-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_readable (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (φ : ℕ → E → EReal),
      (∀ j, ConvexPotential (φ j)) ∧ (∀ j, PotentialIntegrable (φ j) μ) ∧
      (∀ j x, 0 ≤ φ j x) ∧ (∀ j, φ j 0 = 0) ∧
      Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 (S : EReal)) ∧
      ∀ ψ : E → EReal, ConvexPotential ψ → PotentialIntegrable ψ μ →
        (∀ x, 0 ≤ ψ x) → ψ 0 = 0 → variationalFunctional dx μ ψ ≤ (S : EReal) := by sorry
