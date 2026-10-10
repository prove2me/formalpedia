-- Prove2me | Theorems.Thm_NecoaraNG_Compose_theorem_8
-- name    : NecoaraNG.Compose.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:14.726384+00:00
-- url     : https://prove2.me/theorems/bfc2d1db-c815-4b4b-b304-5aa9a20b1a0c
-- title:
--   Theorem 8, p. 14 — g(Ax) with g strongly convex and smooth is in qS(X) with L_f = L_g‖A‖², κ_f = σ_g/θ²(A, C)
-- statement:
--   Let $X=\{x\in\mathbb R^n: Cx\le d\}$ be a polyhedral set, $g:\mathbb R^m\to\mathbb R$ differentiable and $\sigma_g$-strongly convex ($\sigma_g>0$) with $L_g$-Lipschitz continuous gradient, and $A\in\mathbb R^{m\times n}$ a nonzero matrix. Assume problem (38), $\min_{x\in X} g(Ax)$, has an optimal point $x^*$, and let $\theta(A,C)>0$ be a Hoffman constant for the polyhedral optimal set $\{x: Ax=Ax^*,\ Cx\le d\}$. Then $f(x)=g(Ax)$ belongs to the class $q\mathcal S_{L_f,\kappa_f}(X)$ with
--   $$L_f=L_g\|A\|^2,\qquad\kappa_f=\frac{\sigma_g}{\theta^2(A,C)};$$
--   that is, $f$ is convex on $X$, $\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|$ for $x,y\in X$, and for every $x\in X$ and $\bar x=[x]_{X^*}$
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa_f}2\|x-\bar x\|^2.$$
--
--   The theorem shows that strong convexity of $g$ survives composition with a rank-deficient linear map and restriction to a polyhedron in the weaker quasi-strong form, with a constant governed by Hoffman's constant. It is the main example of a non-strongly convex class on which the paper's first order methods converge linearly.
--
--   **Formalization Note** $\|A\|$ is the operator (spectral) norm. Strong convexity is Mathlib's `StrongConvexOn` on all of $\mathbb R^m$, which is (5). The page's "$L_g$-Lipschitz continuous gradient on $X$" is read on $\mathbb R^m$, the domain of $g$. The Hoffman constant is a hypothesis (its existence is Hoffman's theorem, cited by the page); it is stated for the polyhedron written with $Ax^*$, which the proof identifies with $X^*$. The page's "simple" set and "closed" function add no mathematical hypothesis here.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 14, Theorem 8

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace NecoaraNG.Compose

theorem theorem_8 {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (hA : A ≠ 0) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p)
    (d : NecoaraNG.Chain.E p) (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (σg Lg : ℝ) (hσg : 0 < σg)
    (hg : StrongConvexOn Set.univ σg g)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)))
    (θ : ℝ) (hθ : 0 < θ) (hHoff : IsHoffmanConst A C (A xstar) d θ) :
    ConvexOn ℝ (polyhedron C d) (fun x => g (A x)) ∧
      LipGradOn (polyhedron C d) (fun x => g (A x)) (Lg * ‖A‖ ^ 2) ∧
      NecoaraNG.Chain.QuasiStrong (polyhedron C d) (fun x => g (A x)) (σg / θ ^ 2) := by sorry

end NecoaraNG.Compose
