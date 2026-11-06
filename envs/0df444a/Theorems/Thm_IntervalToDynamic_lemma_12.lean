-- Prove2me | Theorems.Thm_IntervalToDynamic_lemma_12
-- name    : IntervalToDynamic.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:10.955206+00:00
-- url     : https://prove2.me/theorems/af7d45e8-607e-45cd-86bc-5672e08612c5
-- title:
--   Lemma 12 — quadratic regret upper bound under exp-concavity
-- statement:
--   Let $f$ be differentiable, $\alpha$-exp-concave and $G$-Lipschitz on a convex domain $S\subseteq\mathbb R^d$ of diameter at most $D$. If
--   $$
--   \gamma\le\frac12\min\Bigl\{\alpha,\frac1{DG}\Bigr\},
--   $$
--   then for every pair $(x,u)$ in the domain,
--   $$
--   f(x)-f(u)\le A-\frac\gamma2A^2,\qquad A=\nabla f(x)^\top(x-u).
--   $$
--
--   This quadratic bound is what the exp-concave surrogate of Eq. (11) is built on.
--
--   **Formalization Note** $G$ is a Lipschitz constant of $f$ on $S$, not a bound on the gradient oracle. The diameter bound is written as $\|x-u\|\le D$ on $S$.
--
--   Differences from the source:
--   - generalization: f differentiable on the domain, with gradient ∇f → any gradient oracle with `HasGradientWithinAt` on the domain; reason: the domain may have empty interior; the gradient of a differentiable loss is such an oracle, so the printed case is included
--   - encoding: α-exp-concave; coefficients 1/(D G) → hypotheses `0 < α`, `0 < D`, `0 < G`; reason: exp-concavity is defined for α > 0 and the printed bound divides by D G
--   - encoding: diameter at most D → `‖x − u‖ ≤ D` for x, u ∈ S; reason: the same condition, without `Metric.diam`
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 12, p.29

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace IntervalToDynamic

/-- Lemma 12 (quadratic regret upper bound under exp-concavity). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 12, p.29.

Let `f` be differentiable, `α`-exp-concave and `G`-Lipschitz on a convex domain `S ⊆ ℝ^d` of diameter
at most `D`. If `γ ≤ ½ min{α, 1/(D G)}`, then for every `x, u ∈ S`,
`f(x) − f(u) ≤ A − (γ/2) A²` with `A = ∇f(x)ᵀ(x − u)`.

**Formalization Note.** The gradient is an oracle within `S`, which may have empty interior. `G` is a
Lipschitz constant of `f` on `S`, as printed, not a bound on the oracle. "Diameter at most `D`" is
`‖x − u‖ ≤ D` on `S`, which avoids the junk value of a diameter function. `0 < α`, `0 < D`, `0 < G` make the printed
coefficients meaningful. -/
theorem lemma_12 {d : ℕ} (hd : 0 < d) (S : Set (EuclideanSpace ℝ (Fin d))) (hS : Convex ℝ S) (f : EuclideanSpace ℝ (Fin d) → ℝ) (gf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (α D G γ : ℝ) (hα : 0 < α) (hD : 0 < D) (hG : 0 < G)
    (hgrad : ∀ x ∈ S, HasGradientWithinAt f (gf x) S x)
    (hexp : LogRegretOCO.ONS.IsExpConcaveOn α S f)
    (hLip : ∀ x ∈ S, ∀ u ∈ S, |f x - f u| ≤ G * ‖x - u‖)
    (hdiam : ∀ x ∈ S, ∀ u ∈ S, ‖x - u‖ ≤ D)
    (hγ : γ ≤ (1 / 2) * min α (1 / (D * G))) (x u : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) (hu : u ∈ S) :
    f x - f u ≤ inner ℝ (gf x) (x - u) - (γ / 2) * (inner ℝ (gf x) (x - u)) ^ 2 := by sorry

end IntervalToDynamic
