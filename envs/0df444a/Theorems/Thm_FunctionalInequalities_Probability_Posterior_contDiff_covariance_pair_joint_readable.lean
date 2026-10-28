-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_covariance_pair_joint_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:00.088116+00:00
-- url     : https://prove2.me/theorems/f0d416e4-4daa-49f4-9fdf-85bc15992dcb
-- title:
--   Joint Smoothness of Posterior Covariances
-- statement:
--   This theorem states the joint $C^\infty$ regularity of posterior covariances of two linear statistics.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with a measurable structure and its Borel structure. Let $\mu$ be a probability measure on $E$ such that its measure-theoretic support is compact. For arbitrary vectors $u,v\in E$, let $p=(c,Q)$ range over $E\times(E\to_L[\mathbb R]E)$, where $c\in E$ and $Q$ is a continuous linear operator from $E$ to $E$. The posterior measure at $p$ is the tilted measure
--   `(μ : Measure E).tilted (quadraticExponent c Q)`.
--
--   The covariance of the linear statistics $x\mapsto\langle u,x\rangle$ and $x\mapsto\langle v,x\rangle$ under this tilted measure is infinitely continuously differentiable jointly in $(c,Q)$:
--
--   $$
--   p\longmapsto \operatorname{Cov}_{\operatorname{tilted}(\mu,\,\operatorname{quadraticExponent}(c,Q))}\bigl(\langle u,X\rangle,\langle v,X\rangle\bigr)\quad\text{is }C^\infty.
--   $$
--
--   This is a technical regularity result that can be reused when differentiating posterior covariance expressions with respect to both the linear parameter and the quadratic operator parameter. It applies to arbitrary $u$ and $v$, including when $Q=0$, and does not require isotropy of the prior.
--
--   **Formalization Note** The conclusion is the Lean predicate `ContDiff ℝ ∞` on the product space $E\times(E\to_L[\mathbb R]E)$, with the operator space carrying its usual operator-norm structure. The covariance is formed with respect to the tilted measure and the statement does not assert any covariance identity beyond its joint smoothness.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_covariance_pair_joint (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (u v : E) :
--       ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
--         covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
--           ((μ : Measure E).tilted (quadraticExponent p.1 p.2)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`contDiff_posteriorExpectation_joint`](https://prove2.me/theorems/26f7270c-a7c7-4be5-ace6-46911a4ce683).
--
--   Previous: [`contDiff_posteriorMean_joint`](https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa) · Next: [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   [Source excerpt, lines 249–253](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L249-L253) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L247-L274 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity

open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (u v : E) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (quadraticExponent p.1 p.2))) := by sorry
