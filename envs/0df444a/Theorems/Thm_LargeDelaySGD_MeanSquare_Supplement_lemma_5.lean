-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_Supplement_lemma_5
-- name    : LargeDelaySGD.MeanSquare.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:10:10.043817+00:00
-- url     : https://prove2.me/theorems/40ed73fb-1e22-41a7-a77d-3f3938008ad3
-- title:
--   Lemma 5, p. 18 — E strictly decreases along the mean-field flow off X*, and drops by δ/2 by time T(δ) (corrected: part 2 needs energy reciprocity)
-- statement:
--   Throughout, $\mathcal X\subseteq\mathbb R^d$ is a nonempty compact convex feasible set, $F(x;\omega)$ a random function with $f(x)=\mathbb E[F(x;\omega)]$, $\nabla f(x)=\mathbb E[\nabla F(x;\omega)]$ on $\mathcal X$, $\mathcal X^*$ the set of minimizers of $f$ over $\mathcal X$, and $\mathrm{pr}_{\mathcal X}$ the Euclidean projection onto $\mathcal X$. Assumption 1 is imposed on $\mathcal X$ only, Assumption 3 is mean variational coherence, and Assumption 4 is the printed implication $E(y_n)\to0\Rightarrow\mathrm{pr}_{\mathcal X}(y_n)\to\mathcal X^*$. A sequence converges to $\mathcal X^*$ when its distance to $\mathcal X^*$ tends to $0$.
--
--   Let $P$ be the semiflow of the mean-field ODE (17), $\dot y=-\nabla f(\mathrm{pr}_{\mathcal X}(y))$, $P(0,y)=y$, and let $E$ be the energy of Definition 1.
--
--   **Lemma 5.**
--
--   1. For every $y\in\mathbb R^d$ and $0\le t<t'$, if $\mathrm{pr}_{\mathcal X}(P(t,y))\notin\mathcal X^*$, then $E(P(t',y))<E(P(t,y))$.
--   2. Assume energy reciprocity: $\mathrm{dist}(\mathrm{pr}_{\mathcal X}(y_n),\mathcal X^*)\to0$ implies $E(y_n)\to0$ for every sequence $(y_n)$. Then for every $\delta>0$ there is $T=T(\delta)>0$ such that, for all $t\ge T$ and all $y\in\mathbb R^d$,
--   $$E(P(t,y))\ge\frac\delta2\quad\Longrightarrow\quad E(P(t,y))-E(y)\le-\frac\delta2 .$$
--
--   Part 2 is the uniform "sufficient decrease" of the energy along the mean dynamics that the proof of Theorem 3 combines with Lemma 6.
--
--   **Formalization Note** The supremum (18) over the set $\{y: E(P(t,y))\ge\delta/2\}$ is written as an implication for each $y$, which is equivalent and avoids a real supremum of an empty set.
--
--   Differences from the source:
--   - correction: Lemma 5 (2) under Assumptions 1–4 with Assumption 4 as printed → part (2) assumes energy reciprocity (pr_X(y_n) → X* implies E(y_n) → 0); part (1) is unchanged; reason: as printed, part (2) is false: on the unit disk X with f(x) = x₂, X* = {(0,−1)}, the points y = R(sin θ, −cos θ) with R(1 − cos θ) = 1 have E(y) = 2 while E(P(t,y)) → 2 as θ → 0 for each fixed t (DISPROOF.md). The proof (p. 36) and footnote 15 (p. 32) use exactly this converse, which p. 14 announces as Assumption 4 ('the converse of Statement 2') and says holds for polytopes; disks and other curved domains on which it fails are excluded
--   - reading: 'E(P(t, y)) is strictly decreasing in t' when pr_X(P(t, y)) ∉ X* → for all t < t', pr_X(P(t,y)) ∉ X* implies E(P(t',y)) < E(P(t,y)); reason: strict decrease from the time t onwards; E is non-increasing along the flow (B.41), so this is the strict monotonicity on the times before X* is reached
--   - encoding: sup_y {E(P(t,y)) − E(y) : E(P(t,y)) ≥ δ/2} ≤ −δ/2 (18) → for every y with E(P(t,y)) ≥ δ/2, E(P(t,y)) − E(y) ≤ −δ/2; reason: equivalent; avoids the real supremum of a possibly empty set
--   - reading: P, the semiflow of the ODE ẏ = −∇f(pr_X(y)) (17), p. 17 → any Flow ℝ≥0 on ℝ^d whose trajectories have right derivative −∇f(pr_X(P(t, y))) at every t ≥ 0; reason: the drift is globally Lipschitz under Assumption 1, so the semiflow exists and is unique; quantifying over every such flow is the source's P
--   - reading: ∇f(x) for x ∈ X, with f defined on X only (Algorithm 5, (6), (17)) → meanGrad F μ x = E[∇F(x; ω)] (a Bochner integral); reason: Remark 1 (p. 5) identifies ∇f with E[∇F]; for f defined only on a compact X the ambient Fréchet gradient may be the junk value 0 at boundary points, the expectation is the source's gradient
--   - reading: Assumption 1 on X: F(·; ω) differentiable for a.a. ω, sup_{x∈X} E‖∇F‖² < ∞, E[∇F] Lipschitz on X → ConstrainedAssumption1: an ambient F(·; ξ) differentiable at every point of X for a.a. ξ, F(x) integrable and ∇F(x) in L² for x ∈ X, ∇F jointly measurable on X × Ξ, a uniform second-moment bound and a Lipschitz mean gradient on X; reason: the source's F lives on X × Ω; its gradient at boundary points presupposes a differentiable extension. Integrability (the expectation in (1) exists) and joint measurability (footnote 1: F is a random function; the iterates must be random variables) only exclude cases where the source's expressions are undefined; nothing is assumed off X
--   - reading: Assumption 4, introduced as 'the converse of Statement 2' of Lemma 3 but printed as: E(y_n) → 0 implies pr_X(y_n) → X* → Assumption4 in its printed direction; reason: the planned reading keeps the displayed statement; it is implied by Lemma 3 (2), so it is a redundant hypothesis. The converse that footnote 15 (p. 32) uses is not assumed
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1 (SHA-256 20dd663845757ad1e06f51c4ae62f8fd6623aa921b66be496b00befa51d9a327), p. 18, Lemma 5 (proof App. B.2.6, p. 36)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_LargeDelaySGD_MeanSquare_Supplement_Constrained

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace LargeDelaySGD.MeanSquare.Supplement

theorem lemma_5 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hXne : X.Nonempty)
    (hA1 : ConstrainedAssumption1 F μ X) (hA3 : VariationallyCoherent F μ X)
    (hA4 : Assumption4 X (solutionSet F μ X))
    (Pf : Flow ℝ≥0 (EuclideanSpace ℝ (Fin d))) (hP : IsMeanFieldFlow F μ X Pf) :
    (∀ (y : EuclideanSpace ℝ (Fin d)) (t t' : ℝ≥0), t < t' →
      proj X (Pf t y) ∉ solutionSet F μ X →
        energy X (solutionSet F μ X) (Pf t' y) < energy X (solutionSet F μ X) (Pf t y)) ∧
    (EnergyReciprocity X (solutionSet F μ X) →
      ∀ δ : ℝ, 0 < δ → ∃ T : ℝ≥0, 0 < T ∧ ∀ t : ℝ≥0, T ≤ t → ∀ y : EuclideanSpace ℝ (Fin d),
        δ / 2 ≤ energy X (solutionSet F μ X) (Pf t y) →
          energy X (solutionSet F μ X) (Pf t y) - energy X (solutionSet F μ X) y ≤ -(δ / 2)) := by sorry

end LargeDelaySGD.MeanSquare.Supplement
