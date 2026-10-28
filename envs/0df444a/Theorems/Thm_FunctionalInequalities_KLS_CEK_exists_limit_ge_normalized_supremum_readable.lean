-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_limit_ge_normalized_supremum_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:24.208822+00:00
-- url     : https://prove2.me/theorems/9ad1f752-005f-403f-b340-5ef5a45400a5
-- title:
--   Normalized Supremum Witness
-- statement:
--   This formalizes the variational-existence part of Proposition 12 of Cordero–Klartag (arXiv:1304.0630v1), in a limit-based form.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace $V\subseteq E$ with $\mu(V^c)=0$ is all of $E$.
--   2. The identity map on $E$ is integrable with respect to $\mu$.
--   3. The barycenter vanishes: $\int x\,d\mu=0$.
--
--   Then there exist $S\in\mathbb{R}$ and a function $\psi:E\to\overline{\mathbb{R}}$ such that $\psi$ is a convex potential, is potential-integrable with respect to $\mu$, is nonnegative, and satisfies $\psi(0)=0$. Its conjugate mass is finite and strictly positive, and
--
--   $$
--   (S:\overline{\mathbb{R}})\le I_{dx,\mu}(\psi),
--   $$
--
--   where `variationalFunctional` is $I_{dx,\mu}$. Moreover, every competitor $\eta$ that is convex, potential-integrable, nonnegative, and satisfies $\eta(0)=0$ obeys
--
--   $$
--   I_{dx,\mu}(\eta)\le S.
--   $$
--
--   This statement supplies a normalized potential whose value reaches the supremum level up to the displayed lower bound and is used to obtain an actual variational maximizer.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_limit_ge_normalized_supremum (dx μ : Measure E)
--       [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       ∃ (S : ℝ) (ψ : E → EReal), ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
--         (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧ 0 < mass dx (legendre ψ) ∧ mass dx (legendre ψ) ≠ ⊤ ∧
--         (S : EReal) ≤ variationalFunctional dx μ ψ ∧
--         ∀ η : E → EReal, ConvexPotential η → PotentialIntegrable η μ →
--           (∀ x, 0 ≤ η x) → η 0 = 0 → variationalFunctional dx μ η ≤ (S : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/VariationalMaximum`](https://prove2.me/theorems/60547a65-c647-4027-80b6-d75ac35d269f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`exists_normalized_maximizing_sequence`](https://prove2.me/theorems/11706c73-d73a-45ce-a370-2f9ff07f3e79), [`exists_integral_bound_of_eventual_functional_lower`](https://prove2.me/theorems/ec1ab899-a2cd-4af7-a22e-cf39c5c47111), [`exists_subseq_integral_bounds_of_convex_epigraph`](https://prove2.me/theorems/475ba44f-a554-43ce-bfd2-ddb53b1e5734), [`log_sub_ge_of_integral_limits`](https://prove2.me/theorems/8c2c9203-7701-486b-b236-68a42ba9b8b5), [`zero_mem_interior_convexHull_support_of_integral_eq_zero`](https://prove2.me/theorems/24d566b9-c33c-4ef2-a315-a7ad900693e2).
--
--   Previous: [`exists_normalized_maximizing_sequence`](https://prove2.me/theorems/11706c73-d73a-45ce-a370-2f9ff07f3e79) · Next: [`exists_variational_maximum`](https://prove2.me/theorems/2658ff47-5952-426e-98f9-f3b3ec7e8d7b).
--
--   [Source excerpt, lines 88–96](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L88-L96) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L85-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_readable (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (ψ : E → EReal), ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧ 0 < mass dx (legendre ψ) ∧ mass dx (legendre ψ) ≠ ⊤ ∧
      (S : EReal) ≤ variationalFunctional dx μ ψ ∧
      ∀ η : E → EReal, ConvexPotential η → PotentialIntegrable η μ →
        (∀ x, 0 ≤ η x) → η 0 = 0 → variationalFunctional dx μ η ≤ (S : EReal) := by sorry
