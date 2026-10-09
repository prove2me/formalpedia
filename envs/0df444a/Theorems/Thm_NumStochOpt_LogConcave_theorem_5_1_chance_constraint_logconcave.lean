-- Prove2me | Theorems.Thm_NumStochOpt_LogConcave_theorem_5_1_chance_constraint_logconcave
-- name    : NumStochOpt.LogConcave.theorem_5_1_chance_constraint_logconcave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:47:34.420333+00:00
-- url     : https://prove2.me/theorems/8a1dca99-fc18-48d1-8997-7982bf1c67dd
-- title:
--   Theorem 5.1 — jointly concave constraints and a log-concave density give a log-concave probability function $h_0$
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and let $\xi : \Omega \to \mathbb R^q$ be a random vector with a continuous (absolutely continuous) probability distribution: there is a measurable density $f : \mathbb R^q \to [0,\infty)$ with $P(\xi \in A) = \int_A f(y)\,dy$ for every Borel set $A \subseteq \mathbb R^q$. Assume $f$ is **logarithmically concave**: for all $y_1, y_2 \in \mathbb R^q$ and $0 < \lambda < 1$,
--
--   $$
--   f(\lambda y_1 + (1-\lambda) y_2) \ge f(y_1)^{\lambda} f(y_2)^{1-\lambda}.
--   $$
--
--   Let $g_1, \dots, g_r : \mathbb R^{n} \times \mathbb R^{q} \to \mathbb R$ be concave functions of the joint variable $(x, y) \in \mathbb R^{n+q}$. Then the probability function
--
--   $$
--   h_0(x) = P\bigl(g_1(x,\xi) \ge 0, \dots, g_r(x,\xi) \ge 0\bigr)
--   $$
--
--   is logarithmically concave on $\mathbb R^n$: for all $x_1, x_2 \in \mathbb R^n$ and $0 < \lambda < 1$, $h_0(\lambda x_1 + (1-\lambda)x_2) \ge h_0(x_1)^{\lambda} h_0(x_2)^{1-\lambda}$.
--
--   In particular, when $\xi$ has a log-concave density the function $x \mapsto P(Tx \ge \xi)$ of (5.2) is log-concave, so the probabilistic constraint $h_0(x) \ge p$ defines a convex set of decisions. The theorem is the basis of the convergence theory of every method of the chapter; the book cites its proof from Prékopa's survey rather than giving it.
--
--   **Formalization Note** The book writes "for every $x_1, x_2 \in \mathbb R^n$" in the density condition; the density lives on $\mathbb R^q$, and the condition is stated there. Concavity of each $g_i$ is joint concavity on the product $\mathbb R^n \times \mathbb R^q$ (concavity in $x$ and in $y$ separately would not suffice). The law of $\xi$ is fixed by `P.map ξ = volume.withDensity (ofReal ∘ f)` with $\xi$ and $f$ measurable. Log-concavity is the platform predicate `ConvexOptimization.LogConcaveOn` (nonnegativity plus the power inequality for all convex weights), which remains meaningful where $h_0$ or $f$ vanish; it is not concavity of `Real.log ∘ h₀`.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, p. 124, Theorem 5.1 (problem (5.1) on p. 123)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_NumStochOpt_LogConcave_chanceProb

open MeasureTheory

namespace NumStochOpt.LogConcave

theorem theorem_5_1_chance_constraint_logconcave
    {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    ConvexOptimization.LogConcaveOn Set.univ (chanceProb P ξ g) := by sorry

end NumStochOpt.LogConcave
