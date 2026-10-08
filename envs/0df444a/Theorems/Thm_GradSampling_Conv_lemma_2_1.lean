-- Prove2me | Theorems.Thm_GradSampling_Conv_lemma_2_1
-- name    : GradSampling.Conv.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:27.836114+00:00
-- url     : https://prove2.me/theorems/3abed632-fe97-4717-aed3-3694b1bd0a28
-- title:
--   Lemma 2.1, p. 756 — −dist(0 | G) = min_{‖d‖≤1} max_{g∈G} ⟨g, d⟩, attained at −ḡ/‖ḡ‖
-- statement:
--   Let $G\subseteq\mathbb R^n$ be a nonempty compact convex set. Then
--
--   $$-\operatorname{dist}(0\mid G)=\min_{\|d\|\le1}\ \max_{g\in G}\ \langle g,d\rangle ,$$
--
--   where both the inner maximum and the outer minimum are attained. Moreover, if $\bar g\in G$ satisfies $\|\bar g\|=\operatorname{dist}(0\mid G)$, then $\bar d=-\bar g/\|\bar g\|$ has $\|\bar d\|\le 1$ and attains the minimum on the right-hand side.
--
--   Applied to $G=G_k$, this says that the GS search direction $d^k=-g^k/\|g^k\|$ is an approximate direction of steepest descent.
--
--   **Formalization Note** "min" and "max" are encoded with `IsLeast`/`IsGreatest`, which assert attainment. Nonemptiness of $G$ is added: the maximum over $G$ presupposes it. When $\bar g=0$, Lean's convention $0^{-1}=0$ gives $\bar d=0$, which is then indeed a minimizer.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 756, Lemma 2.1, display (3)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Lemma 2.1, p. 756: for a compact convex `G ⊆ ℝⁿ`,
`−dist(0 | G) = min_{‖d‖ ≤ 1} max_{g ∈ G} ⟨g, d⟩`, and if `ḡ ∈ G` has `‖ḡ‖ = dist(0 | G)` then
`d̄ = −ḡ/‖ḡ‖` attains the outer minimum. `G` nonempty is added: the inner max presupposes it. -/
theorem lemma_2_1 {n : ℕ} (G : Set (EuclideanSpace ℝ (Fin n))) (hGc : IsCompact G) (hGcv : Convex ℝ G)
    (hGne : G.Nonempty) :
    IsLeast {s : ℝ | ∃ d : EuclideanSpace ℝ (Fin n), ‖d‖ ≤ 1 ∧ IsGreatest ((fun g => inner ℝ g d) '' G) s}
        (-Metric.infDist 0 G) ∧
      ∀ gbar ∈ G, ‖gbar‖ = Metric.infDist 0 G →
        ‖-(‖gbar‖⁻¹ • gbar)‖ ≤ 1 ∧
          IsGreatest ((fun g => inner ℝ g (-(‖gbar‖⁻¹ • gbar))) '' G) (-Metric.infDist 0 G) := by sorry

end GradSampling.Conv
