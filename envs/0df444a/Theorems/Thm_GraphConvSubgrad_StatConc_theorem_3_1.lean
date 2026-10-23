-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_theorem_3_1
-- name    : GraphConvSubgrad.StatConc.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:13.696603+00:00
-- url     : https://prove2.me/theorems/39754499-3809-4ffd-845e-0747e0070a17
-- title:
--   Theorem 3.1, pp. 10–11 — smoothness of the Φ-envelope: unique Φ-proximal point and gradient (1/λ)∇²Φ(x)(x − prox)
-- statement:
--   Let $\Phi$ be a Legendre function on a finite-dimensional real normed space $E$, and let $g:E\to\mathbb R\cup\{+\infty\}$ be closed, bounded below, proper with convex domain, $\rho$-weakly convex relative to $\Phi$ (that is, $g+\rho\Phi$ is convex), and compatible with $\Phi$ ($\operatorname{ri}(\operatorname{dom} g)\subseteq\operatorname{int}(\operatorname{dom}\Phi)$). Let $\lambda>0$ with $\lambda\rho<1$ and $x\in\operatorname{int}(\operatorname{dom}\Phi)$. Then:
--
--   1. the Φ-proximal point
--   $$\operatorname{prox}^\Phi_{\lambda g}(x)=\operatorname*{argmin}_y\Big\{g(y)+\tfrac1\lambda D_\Phi(y,x)\Big\}$$
--   is a single point $p$, and $p\in\operatorname{dom} g\cap\operatorname{int}(\operatorname{dom}\Phi)$;
--   2. if $\Phi$ is twice differentiable on $\operatorname{int}(\operatorname{dom}\Phi)$, the Φ-envelope $g^\Phi_\lambda(x)=\inf_y\{g(y)+\frac1\lambda D_\Phi(y,x)\}$ is differentiable at $x$ with
--   $$\nabla g^\Phi_\lambda(x)=\tfrac1\lambda\nabla^2\Phi(x)\big(x-\operatorname{prox}^\Phi_{\lambda g}(x)\big).$$
--
--   This is the paper's Theorem 3.1, which it attributes to [10] and [17, Theorem 4.1]. Every later statement uses it: it makes the proximal maps of $\varphi$ and $\varphi_S$ single-valued, places them where (A1) and (A3) apply, and turns distances between proximal points into distances between envelope gradients.
--
--   **Formalization Note** The paper writes "positive $\lambda<\rho^{-1}$", which parses only for $\rho>0$; the hypothesis $0<\lambda$, $\lambda\rho<1$ covers every real $\rho$. The paper's "$\Phi:\mathbb R^d\to\{\infty\}$" is read as $\mathbb R\cup\{\infty\}$. Added hypotheses: $\operatorname{dom} g$ is nonempty (a function with empty domain has no proximal point) and convex (for a nonconvex domain the relative interior can be empty, compatibility is then vacuous, and the proximal point can sit on the boundary of $\operatorname{dom}\Phi$). The proximal map is the set `proxSet Φ g (1/λ) x` and the first conclusion says it equals $\{p\}$. Twice differentiability is differentiability of $x\mapsto\nabla\Phi(x)$ on the interior; $\nabla^2\Phi(x)(x-p)$ is the second Fréchet derivative applied to $x-p$, an element of $E^*$.
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, pp. 10–11, Theorem 3.1, (3.3)

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

open MeasureTheory

/-- Theorem 3.1 (Smoothness of the Φ-envelope), pp. 10–11. For a closed, lower-bounded `g` that is
`ρ`-weakly convex relative to and compatible with a Legendre `Φ`, every `0 < λ` with `λ ρ < 1`
and every `x ∈ int (dom Φ)`: the proximal point `prox^Φ_{λ g}(x)` (here `proxSet Φ g (1/λ) x`) is a
single point `p ∈ dom g ∩ int (dom Φ)`; and if `Φ` is twice differentiable on `int (dom Φ)`, the
envelope `g^Φ_λ` is differentiable at `x` with gradient `(1/λ) ∇²Φ(x)(x − p)`. Added: `dom g` is
nonempty and convex. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ g : ExtFn E) (ρ : ℝ) (hΦ : IsLegendre Φ)
    (hg_closed : g.IsClosed) (hg_bdd : BddBelow (g.val '' g.dom))
    (hg_wc : WeaklyConvexRel Φ g ρ) (hg_compat : Compatible Φ g)
    (hg_proper : g.dom.Nonempty) (hg_convex : Convex ℝ g.dom)
    (lam : ℝ) (hlam : 0 < lam) (hlamρ : lam * ρ < 1)
    (x : E) (hx : x ∈ interior Φ.dom) :
    ∃ p : E, proxSet Φ g (1 / lam) x = {p} ∧ p ∈ g.dom ∩ interior Φ.dom ∧
      (DifferentiableOn ℝ (fderiv ℝ Φ.val) (interior Φ.dom) →
        HasFDerivAt (envelope Φ g (1 / lam))
          ((1 / lam) • (fderiv ℝ (fderiv ℝ Φ.val) x) (x - p)) x) := by sorry

end GraphConvSubgrad.StatConc
