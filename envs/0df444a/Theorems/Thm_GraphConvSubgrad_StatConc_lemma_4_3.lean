-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_lemma_4_3
-- name    : GraphConvSubgrad.StatConc.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:21.160397+00:00
-- url     : https://prove2.me/theorems/a3ffec11-e895-4b04-866e-9c242f93fb18
-- title:
--   Lemma 4.3, p. 15 — the Bregman proximal map is ρ̄/(α(ρ̄−ρ))-Lipschitz in the metric ‖∇Φ(x) − ∇Φ(y)‖∗
-- statement:
--   Let $\Phi$ be a Legendre function on a finite-dimensional real normed space $E$ and let $g:E\to\mathbb R\cup\{+\infty\}$ be closed, bounded below, proper with convex domain, $\rho$-weakly convex relative to $\Phi$ and compatible with $\Phi$. Assume that $\Phi$ is $\alpha$-strongly convex on $\operatorname{dom} g\cap\operatorname{int}(\operatorname{dom}\Phi)$ for some $\alpha>0$, in the sense
--   $$\frac\alpha2\|v-u\|^2\le D_\Phi(u,v)\qquad\text{for all }u,v\in\operatorname{dom} g\cap\operatorname{int}(\operatorname{dom}\Phi).$$
--   Then for every $\bar\rho>\max(\rho,0)$ and all $x,y\in\operatorname{int}(\operatorname{dom}\Phi)$,
--   $$\big\|\operatorname{prox}^\Phi_{g/\bar\rho}(x)-\operatorname{prox}^\Phi_{g/\bar\rho}(y)\big\|\le\frac{\bar\rho}{\alpha(\bar\rho-\rho)}\,\|\nabla\Phi(x)-\nabla\Phi(y)\|_*.$$
--
--   This is the Lipschitz estimate that lets the proof of Theorem 4.4 pass from finitely many centres of a covering to all of $C$, in the metric $d_\Phi(x,y)=\|\nabla\Phi(x)-\nabla\Phi(y)\|_*$.
--
--   **Formalization Note** The inequality is stated for every point of the proximal set at $x$ and every point of the one at $y$ (Theorem 3.1 shows they are singletons). $\|\cdot\|_*$ is the operator norm of the Fréchet derivatives. Added: $\operatorname{dom} g$ nonempty and convex (as in Theorem 3.1), $\alpha>0$, and $\bar\rho>0$ ($\bar\rho$ multiplies $D_\Phi$ in the proximal map; for $\bar\rho\le0$ the right side is not a Lipschitz bound).
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, p. 15, Lemma 4.3

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

/-- Lemma 4.3 (Lipschitz continuity), p. 15. For a closed, lower-bounded `g` that is `ρ`-weakly
convex relative to and compatible with a Legendre `Φ`, with `Φ` `α`-strongly convex on
`dom g ∩ int (dom Φ)` (`(α/2)‖v − u‖² ≤ D_Φ(u, v)`), every `ρ̄ > ρ` and `x, y ∈ int (dom Φ)`:
`‖prox^Φ_{g/ρ̄}(x) − prox^Φ_{g/ρ̄}(y)‖ ≤ ρ̄ / (α(ρ̄ − ρ)) ‖∇Φ(x) − ∇Φ(y)‖_*`, for every pair of
points of the two proximal sets. Added: `dom g` nonempty and convex, `0 < α`, `0 < ρ̄`. -/
theorem lemma_4_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ g : ExtFn E) (ρ α : ℝ) (hΦ : IsLegendre Φ)
    (hg_closed : g.IsClosed) (hg_bdd : BddBelow (g.val '' g.dom))
    (hg_wc : WeaklyConvexRel Φ g ρ) (hg_compat : Compatible Φ g)
    (hg_proper : g.dom.Nonempty) (hg_convex : Convex ℝ g.dom)
    (hα : 0 < α)
    (hstrong : ∀ u ∈ g.dom ∩ interior Φ.dom, ∀ v ∈ g.dom ∩ interior Φ.dom,
      α / 2 * ‖v - u‖ ^ 2 ≤ bregman Φ u v)
    (rhoBar : ℝ) (hρ : ρ < rhoBar) (hρ0 : 0 < rhoBar)
    (x y : E) (hx : x ∈ interior Φ.dom) (hy : y ∈ interior Φ.dom) :
    ∀ a ∈ proxSet Φ g rhoBar x, ∀ b ∈ proxSet Φ g rhoBar y,
      ‖a - b‖ ≤ rhoBar / (α * (rhoBar - ρ)) * ‖fderiv ℝ Φ.val x - fderiv ℝ Φ.val y‖ := by sorry

end GraphConvSubgrad.StatConc
