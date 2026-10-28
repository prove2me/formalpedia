-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_cap_lsc_readable
-- name    : FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:27.351167+00:00
-- url     : https://prove2.me/theorems/61b64964-9e43-4c79-b57f-0563307ceef2
-- title:
--   Lower-Semicontinuous Capped Optimizer
-- statement:
--   This is a normalized capped-source construction for a bounded isotropic probability law.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be a probability measure on $E$, and let $L\in[0,\infty)$. Assume $\mu$ is isotropic and
--
--   $$
--   \|y\|\le L\quad\text{for $\mu$-almost every }y.
--   $$
--
--   Then there exists $q:E\to\overline{\mathbb{R}}$ such that:
--
--   1. $q$ is a convex lower-semicontinuous potential and is potential-integrable under $\mu$.
--   2. If $q(y)<\infty$, then $y\in\overline{B}(0,L)$.
--   3. Its conjugate mass with respect to Lebesgue measure is one:
--
--   $$
--   \operatorname{mass}_{dx}(q^*)=1.
--   $$
--
--   4. Every potential-integrable competitor $f$ satisfies
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(q).
--   $$
--
--   The declaration is a reusable capped optimizer interface retaining convexity, lower semicontinuity, integrability, normalization, and maximality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bounded_source_cap_lsc
--       (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
--       (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
--       ∃ q : E → EReal,
--         ConvexPotential q ∧
--         LowerSemicontinuous q ∧
--         PotentialIntegrable q (μ : Measure E) ∧
--         (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
--         mass (volume : Measure E) (legendre q) = 1 ∧
--         ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
--           variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
--             variationalFunctional (volume : Measure E) (μ : Measure E) q
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/BoundedPrimal`](https://prove2.me/theorems/9d6c6c4d-d34a-48a4-9377-2f50d4a22e15).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`closedBallCap_lowerSemicontinuous`](https://prove2.me/theorems/de51ab97-7601-407d-8eec-11705d7f5fe2), [`exists_variational_maximum`](https://prove2.me/theorems/2658ff47-5952-426e-98f9-f3b3ec7e8d7b).
--
--   Next: [`bounded_source_finite_conjugate`](https://prove2.me/theorems/ed4d54b9-0112-4d01-8e4a-7196b58fe704).
--
--   [Source excerpt, lines 45–56](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L45-L56) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L42-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.BoundedPrimal`, declaration `FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal

open MeasureTheory Set Metric
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc_readable
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ q : E → EReal,
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by sorry
