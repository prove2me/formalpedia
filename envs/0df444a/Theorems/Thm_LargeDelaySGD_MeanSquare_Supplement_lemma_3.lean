-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_Supplement_lemma_3
-- name    : LargeDelaySGD.MeanSquare.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:07:24.753915+00:00
-- url     : https://prove2.me/theorems/f19afd1f-947f-4d89-976c-6636c4c77adf
-- title:
--   Lemma 3, p. 13 — E ≥ 0 with E(y) = 0 iff pr_X(y) ∈ X*, and E(y_n) → 0 implies pr_X(y_n) → X*
-- statement:
--   Throughout, $\mathcal X\subseteq\mathbb R^d$ is a nonempty compact convex feasible set, $F(x;\omega)$ a random function with $f(x)=\mathbb E[F(x;\omega)]$, $\nabla f(x)=\mathbb E[\nabla F(x;\omega)]$ on $\mathcal X$, $\mathcal X^*$ the set of minimizers of $f$ over $\mathcal X$, and $\mathrm{pr}_{\mathcal X}$ the Euclidean projection onto $\mathcal X$. Assumption 1 is imposed on $\mathcal X$ only, Assumption 3 is mean variational coherence, and Assumption 4 is the printed implication $E(y_n)\to0\Rightarrow\mathrm{pr}_{\mathcal X}(y_n)\to\mathcal X^*$. A sequence converges to $\mathcal X^*$ when its distance to $\mathcal X^*$ tends to $0$.
--
--   **Lemma 3.** Let $E$ be the energy of Definition 1. For every $y\in\mathbb R^d$:
--
--   1. $E(y)\ge0$, and $E(y)=0$ if and only if $\mathrm{pr}_{\mathcal X}(y)\in\mathcal X^*$;
--   2. for every sequence $(y_n)$ in $\mathbb R^d$,
--   $$\lim_{n\to\infty}E(y_n)=0\quad\Longrightarrow\quad\lim_{n\to\infty}\mathrm{dist}\big(\mathrm{pr}_{\mathcal X}(y_n),\mathcal X^*\big)=0 .$$
--
--   The energy is the Lyapunov-type function of the deterministic and stochastic convergence proofs: part 1 makes it a measure of optimality of the dual variable $y$, part 2 turns energy decay into convergence of the primal iterates.
--
--   **Formalization Note** Assumption 1 on $\mathcal X$ is kept: it makes $f$ continuous on $\mathcal X$, so that $\mathcal X^*$ is nonempty and compact.
--
--   Differences from the source:
--   - generalization: Lemma 3 inside §4, whose problems satisfy Assumptions 1–4 → only X nonempty compact convex and Assumption 1 on X; Assumptions 2–4 are not assumed; reason: the lemma concerns only X, X* and the energy; adding Assumptions 2–4 specializes it to the source's setting
--   - reading: Assumption 1 on X: F(·; ω) differentiable for a.a. ω, sup_{x∈X} E‖∇F‖² < ∞, E[∇F] Lipschitz on X → ConstrainedAssumption1: an ambient F(·; ξ) differentiable at every point of X for a.a. ξ, F(x) integrable and ∇F(x) in L² for x ∈ X, ∇F jointly measurable on X × Ξ, a uniform second-moment bound and a Lipschitz mean gradient on X; reason: the source's F lives on X × Ω; its gradient at boundary points presupposes a differentiable extension. Integrability (the expectation in (1) exists) and joint measurability (footnote 1: F is a random function; the iterates must be random variables) only exclude cases where the source's expressions are undefined; nothing is assumed off X
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1 (SHA-256 20dd663845757ad1e06f51c4ae62f8fd6623aa921b66be496b00befa51d9a327), p. 13, Lemma 3 (proof App. B.2.1, pp. 27–28)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_LargeDelaySGD_MeanSquare_Supplement_Constrained

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace LargeDelaySGD.MeanSquare.Supplement

theorem lemma_3 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hXne : X.Nonempty)
    (hA1 : ConstrainedAssumption1 F μ X) :
    (∀ y : EuclideanSpace ℝ (Fin d),
      0 ≤ energy X (solutionSet F μ X) y ∧
        (energy X (solutionSet F μ X) y = 0 ↔ proj X y ∈ solutionSet F μ X)) ∧
    ∀ ys : ℕ → EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => energy X (solutionSet F μ X) (ys n)) atTop (𝓝 0) →
        Tendsto (fun n => Metric.infDist (proj X (ys n)) (solutionSet F μ X)) atTop (𝓝 0) := by sorry

end LargeDelaySGD.MeanSquare.Supplement
