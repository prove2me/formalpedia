-- Prove2me | Theorems.Thm_NesterovRCD_Constrained_eq_4_7
-- name    : NesterovRCD.Constrained.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:11.747638+00:00
-- url     : https://prove2.me/theorems/2d4af219-d06e-4058-9048-734552cef8e4
-- title:
--   (4.7) — the one-step Lyapunov inequality for UCDM
-- statement:
--   In the setting of §4 — $Q=Q_1\times\cdots\times Q_n$ with each $Q_i\subseteq\mathbb R^{n_i}$ nonempty, closed and convex, Euclidean block norms (3.4), and $f$ convex with coordinate-wise Lipschitz gradient (2.2), constants $L_i>0$ — let $V_i$ be the constrained coordinate update (4.2), let $x_*$ be an optimal solution of (4.1) with $f^*=f(x_*)$, and let $\|\cdot\|_1$ be the norm (3.5), $\|h\|_1^2=\sum_iL_i\|h^{(i)}\|_{(i)}^2$. For a feasible point $x\in Q$, let the next iterate be $V_i(x)$ with $i$ drawn uniformly from $\{1,\dots,n\}$. Then
--   $$\frac1n\sum_{i=1}^n\Big(\tfrac12\|V_i(x)-x_*\|_1^2+f(V_i(x))-f^*\Big)\le\tfrac12\|x-x_*\|_1^2+f(x)-f^*+\frac1n\langle\nabla f(x),x_*-x\rangle .$$
--
--   In the paper's notation, with $x=x_k$ and $r_k=\|x_k-x_*\|_1$, this is $\mathbb E_{i_k}\big(\tfrac12r_{k+1}^2+f(x_{k+1})-f^*\big)\le\tfrac12r_k^2+f(x_k)-f^*+\tfrac1n\langle\nabla f(x_k),x_*-x_k\rangle$. Both rates of Theorem 5 are obtained from it.
--
--   **Formalization Note** The expectation over the uniform draw $i_k$ is written out as the average over the $n$ blocks, and the inequality is stated for an arbitrary feasible point $x$ in place of the iterate $x_k$ (the iterates of UCDM started in $Q$ are feasible). $\langle\nabla f(x),y\rangle$ is the Fréchet derivative of $f$ at $x$ applied to $y$. The standing assumptions of §4 are stated as for (4.3), together with $Q_i\ne\emptyset$ and $n\ge1$. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 14, proof of Theorem 5, (4.7)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem eq_4_7 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (xs : NesterovRCD.Sublinear.Blocks E) (hxs : IsMinimizerOn f Q xs)
    (x : NesterovRCD.Sublinear.Blocks E) (hx : x ∈ Qset Q) :
    ∑ i, (n : ℝ)⁻¹ * (NesterovRCD.Sublinear.wnorm L 1 (constrStep f L Q i x - xs) ^ 2 / 2
        + f (constrStep f L Q i x) - f xs)
      ≤ NesterovRCD.Sublinear.wnorm L 1 (x - xs) ^ 2 / 2 + f x - f xs + (n : ℝ)⁻¹ * fderiv ℝ f x (xs - x) := by sorry

end NesterovRCD.Constrained
