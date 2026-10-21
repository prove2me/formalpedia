-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_lemma_3_1
-- name    : MaxValSens.Wolfe.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:23.338137+00:00
-- url     : https://prove2.me/theorems/85ff7c92-fd8e-4484-af83-a57fefb953d2
-- title:
--   Lemma 3.1, p. 16 — Wolfe weak duality V(x) ≤ V_D(x)
-- statement:
--   Fix a parameter $x\in\mathbb R^n$. Suppose $y\mapsto f(x,y)$ is concave and differentiable on $\mathbb R^m$ and every $y\mapsto g_i(x,y)$, $i=1,\dots,q$, is convex and differentiable on $\mathbb R^m$. Let $V(x)=\sup\{f(x,y):g(x,y)\le0\}$ be the maximal value and $V_D(x)=\inf\{\mathcal L(x,y,\lambda):\nabla_y\mathcal L(x,y,\lambda)=0,\ \lambda\ge0\}$ the value of the Wolfe dual, where $\mathcal L(x,y,\lambda)=f(x,y)-g(x,y)^\top\lambda$. Then
--
--   $$V(x)\le V_D(x).$$
--
--   This weak duality lets the maximal value function be bounded above by the value of a minimization problem, which is how Theorem 3.3 turns a maximal value function into a minimal one.
--
--   **Formalization Note** Values are in $[-\infty,+\infty]$ (`EReal`). The paper states the lemma for every $x$ under concavity/convexity in $y$; it is stated here at one fixed $x$, which is the same statement pointwise. Differentiability in $y$ is assumed because the dual is written with $\nabla_y$ (the paper assumes continuous differentiability throughout).
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, p. 16, Lemma 3.1, (3.10)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Lemma 3.1 (Wolfe weak duality), p. 16, at a single parameter `x`: if `f(x, ·)` is concave and
differentiable and every `gᵢ(x, ·)` is convex and differentiable, then `V(x) ≤ V_D(x)`. -/
theorem lemma_3_1 {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n)
    (hfc : ConcaveOn ℝ Set.univ (f x)) (hgc : ∀ i, ConvexOn ℝ Set.univ (g i x))
    (hfd : Differentiable ℝ (f x)) (hgd : ∀ i, Differentiable ℝ (g i x)) :
    V f g x ≤ VD f g x := by sorry

end MaxValSens.Wolfe
