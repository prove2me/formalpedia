-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_finite_conjugate_readable
-- name    : FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:23.215376+00:00
-- url     : https://prove2.me/theorems/ed4d54b9-0112-4d01-8e4a-7196b58fe704
-- title:
--   Finite Conjugate for a Bounded Isotropic Source
-- statement:
--   This is a technical endpoint for a bounded isotropic source law.
--
--   Let $E$ be finite-dimensional with its real inner-product and Borel structures, let $\mu$ be an isotropic probability measure, and let $L\in[0,\infty)$. Assume $\|y\|\le L$ for $\mu$-almost every $y$. Then there exist a potential $q:E\to\overline{\mathbb{R}}$, a point $a\in E$, real numbers $m\in\mathbb{R}$, and $\psi:E\to\mathbb{R}$ such that:
--
--   1. $q$ is convex, lower semicontinuous, and potential-integrable; its finite effective domain lies in $\overline{B}(0,L)$.
--   2. $a\in\overline{B}(0,L)$, $q(a)=m$, and $m\le q(y)$ for every $y$.
--   3. For every $x$, $q^*(x)$ is neither $+\infty$ nor $-\infty$, and
--
--   $$
--   q^*(x)\le L\|x\|-m.
--   $$
--
--   4. $\psi(x)=(q^*(x)).toReal$ and $q^*(x)=\psi(x)$ as an extended-real coercion.
--   5. $\operatorname{mass}_{dx}(q^*)=1$, and every potential-integrable competitor $f$ satisfies
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(q).
--   $$
--
--   This declaration establishes global finiteness of the conjugate and its real representative, but not convexity or Lipschitz regularity of $\psi$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bounded_source_finite_conjugate
--       (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
--       (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
--       ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
--         ConvexPotential q ∧
--         LowerSemicontinuous q ∧
--         PotentialIntegrable q (μ : Measure E) ∧
--         (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
--         a ∈ closedBall (0 : E) (L : ℝ) ∧
--         q a = (m : EReal) ∧
--         (∀ y, (m : EReal) ≤ q y) ∧
--         (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
--         (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
--         ψ = (fun x => (legendre q x).toReal) ∧
--         (∀ x, legendre q x = (ψ x : EReal)) ∧
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
--   Supporting theorems: [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183), [`exists_real_global_minimum_of_bounded_domain`](https://prove2.me/theorems/7afbf80a-1864-49d4-8e93-ff4674a5643f), [`legendre_le_of_real_lower_bound`](https://prove2.me/theorems/36c3f5d5-3ca4-4d66-abff-68d4394870f7), [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1), [`bounded_source_cap_lsc`](https://prove2.me/theorems/61b64964-9e43-4c79-b57f-0563307ceef2).
--
--   Previous: [`bounded_source_cap_lsc`](https://prove2.me/theorems/61b64964-9e43-4c79-b57f-0563307ceef2) · Next: [`bounded_source_lipschitz_primal`](https://prove2.me/theorems/4d577172-78b7-4778-9049-c25519fd30dc).
--
--   [Source excerpt, lines 237–255](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L237-L255) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L232-L278 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.BoundedPrimal`, declaration `FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal

open MeasureTheory Set Metric
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_readable
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
      (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (legendre q x).toReal) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by sorry
