-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_lipschitz_primal_readable
-- name    : FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:23.149616+00:00
-- url     : https://prove2.me/theorems/4d577172-78b7-4778-9049-c25519fd30dc
-- title:
--   Normalized Lipschitz Primal
-- statement:
--   This is a normalized primal construction for a bounded isotropic source law.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be an isotropic probability measure, and let $L\in[0,\infty)$. Assume $\|y\|\le L$ for $\mu$-almost every $y$. Then there exist $q:E\to\overline{\mathbb{R}}$, $a\in E$, $m\in\mathbb{R}$, and $\psi:E\to\mathbb{R}$ satisfying all of the finite-conjugate conclusions: $q$ is convex, lower semicontinuous, potential-integrable, finite only inside $\overline{B}(0,L)$, has a minimum $q(a)=m$, and $m\le q$. Its conjugate is everywhere finite and obeys
--
--   $$
--   q^*(x)\le L\|x\|-m,
--   \qquad q^*(x)=\psi(x).
--   $$
--
--   In addition,
--
--   $$
--   \operatorname{mass}_{dx}(q^*)=1,
--   $$
--
--   $\psi$ is convex and $L$-Lipschitz, and $\psi$ is continuous. Moreover,
--
--   $$
--   \int e^{-\psi(x)}\,dx=1,
--   $$
--
--   and the corresponding weighted measure is a probability measure. Every potential-integrable competitor $f$ satisfies
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(q).
--   $$
--
--   This is a weak normalized convex-Lipschitz primal; it does not assert a gradient pushforward or smoothness beyond the stated continuity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bounded_source_lipschitz_primal
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
--         ConvexOn ℝ (univ : Set E) ψ ∧
--         LipschitzWith L ψ ∧
--         Continuous ψ ∧
--         Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
--         (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
--         IsProbabilityMeasure
--           (weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
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
--   Supporting theorems: [`lipschitzWith_real_legendre`](https://prove2.me/theorems/a855a68c-6e7d-4b04-a93c-aa344c92d581), [`real_convexOn_legendre`](https://prove2.me/theorems/fbb08d4f-988c-4d02-8aba-5ffd7f1a1919), [`bounded_source_finite_conjugate`](https://prove2.me/theorems/ed4d54b9-0112-4d01-8e4a-7196b58fe704), [`real_legendre_normalization`](https://prove2.me/theorems/c3394fe1-6941-4e93-a4a1-c77d84338af6).
--
--   Previous: [`bounded_source_finite_conjugate`](https://prove2.me/theorems/ed4d54b9-0112-4d01-8e4a-7196b58fe704).
--
--   [Source excerpt, lines 284–309](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L284-L309) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L280-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.BoundedPrimal`, declaration `FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal

open MeasureTheory Set Metric
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_readable
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
      ConvexOn ℝ (univ : Set E) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by sorry
