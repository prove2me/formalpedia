-- Prove2me | Theorems.Thm_ManIAL_lemma_3_3
-- name    : ManIAL.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:14.138867+00:00
-- url     : https://prove2.me/theorems/9ade78b3-b08d-412f-869d-76c28d85cf72
-- title:
--   Lemma 3.3 — $\psi_k$ has bounded gradient on $\mathcal M$ and is retr-smooth
-- statement:
--   Suppose Assumption 1 holds: $\mathcal M\subseteq\mathbb R^n$ is compact with a retraction satisfying (2.1) with $\alpha,\beta>0$, $f$ is differentiable with $\ell_{\nabla f}$-Lipschitz gradient, $h$ is convex and $\ell_h$-Lipschitz, $\mathcal A$ is linear and $\varphi=f+h\circ\mathcal A$ is bounded below on $\mathcal M$. Let $\sigma>0$, $z\in\mathbb R^m$ and $\psi=\mathcal L_\sigma(\cdot,z)$. Then
--
--   1. there is a finite $G$ with $\|\nabla\psi(x)\|\le G$ for all $x\in\mathcal M$;
--   2. for every such $G$, $\psi$ is retr-smooth with constant $L=\alpha^2(\ell_{\nabla f}+\sigma\|\mathcal A\|^2)+2G\beta$:
--   $$
--   \psi(R_x(\eta))\le\psi(x)+\langle\eta,\operatorname{grad}\psi(x)\rangle+\frac L2\|\eta\|^2\qquad(x\in\mathcal M,\ \eta\in T_x\mathcal M).
--   $$
--
--   This is what lets ManIAL run Riemannian gradient descent on each subproblem $\psi_k$ with stepsize $1/L_k$.
--
--   Differences from the source:
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ with a retraction R → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, R any map with R_x(T_xM) ⊆ M and the bounds (2.1) for some α, β > 0; reason: §3 uses (M, R) only through these properties; Proposition 2.2 gives them for every retraction on a compact submanifold, so the paper's setting is a special case
--   - generalization: there exists G with ‖∇ψ_k‖ ≤ G on M such that ψ_k is retr-smooth with L_k → ∃ G with the bound, and every G with the bound gives retr-smoothness with L(G); reason: implies the printed statement
--   - generalization: ψ_k = 𝓛_{σ_k}(·, z^k) for the k-th iterate → ψ = 𝓛_σ(·, z) for every σ > 0 and z; reason: contains every iterate
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Lemma 3.3, display (3.22), p.11

import Mathlib
import Definitions.Def_ManIAL_RetrBounds
import Definitions.Def_ManIAL_IsRetrSmooth
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_Lk

namespace ManIAL

/-- **Lemma 3.3** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.11). Under Assumption 1, for
`σ > 0`, `z ∈ ℝᵐ` and `ψ = 𝓛_σ(·, z)`:
1. there is a finite `G` with `‖∇ψ(x)‖ ≤ G` for all `x ∈ M`;
2. for every such `G`, `ψ` is retr-smooth (3.22) with constant
   `L = α²(ℓ_{∇f} + σ‖A‖²) + 2Gβ`.

**Formalization Note.** `M` is a compact set and `R` any map satisfying the bounds (2.1) on
tangent vectors (`RetrBounds`), which is what Proposition 2.2 provides for a retraction on a
compact submanifold. `ℓ_{∇f}`-smooth means differentiable with `ℓ_{∇f}`-Lipschitz gradient.
Part 2 holds for every admissible `G`, which contains the printed "there exists `G` … and `ψ_k` is
retr-smooth with `L_k`". -/
theorem lemma_3_3 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M)
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hR : RetrBounds M R α β)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (σ : ℝ) (hσ : 0 < σ) (z : EuclideanSpace ℝ (Fin m)) :
    (∃ G : ℝ, ∀ x ∈ M, ‖gradient (psi f h A σ z) x‖ ≤ G) ∧
    (∀ G : ℝ, (∀ x ∈ M, ‖gradient (psi f h A σ z) x‖ ≤ G) →
      IsRetrSmooth M R (psi f h A σ z) (Lk α β G ℓf A σ)) := by sorry

end ManIAL
