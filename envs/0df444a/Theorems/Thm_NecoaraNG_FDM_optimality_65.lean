-- Prove2me | Theorems.Thm_NecoaraNG_FDM_optimality_65
-- name    : NecoaraNG.FDM.optimality_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:44.747212+00:00
-- url     : https://prove2.me/theorems/b67d6fd1-503a-4be3-9cc4-56bca0d6cf44
-- title:
--   (65), p. 29 — optimality condition of the projection step of (FDM)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex, $f:\mathbb R^n\to\mathbb R$, and let $(x^k)$, $(e^k)$, $(\alpha_k)$ be a run of the feasible descent method (FDM), so that $x^{k+1}=[x^k-\alpha_k\nabla f(x^k)+e^k]_X$ for every $k\ge0$. Then for every $k\ge0$
--   $$
--   \big\langle x^{k+1}-x^k+\alpha_k\nabla f(x^k)-e^k,\ x-x^{k+1}\big\rangle\ \ge\ 0\qquad\text{for all } x\in X .
--   $$
--
--   This is the variational characterization of the Euclidean projection onto a convex set, applied to the point $x^k-\alpha_k\nabla f(x^k)+e^k$; it is the first step of the proof of Theorem 15.
--
--   **Formalization Note** Only convexity of $X$ and the projection clause of the run are needed: closedness of $X$, convexity and smoothness of $f$, and the positivity of $\beta$, $L$, $\bar L_f$ are dropped because the inequality holds without them. $\nabla f$ is Mathlib's `gradient`.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 29, proof of Theorem 15, (65)

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- (65), proof of Theorem 15, p. 29: the optimality condition of the projection defining
`x^{k+1}`, i.e. `⟪x^{k+1} - x^k + α_k ∇f(x^k) - e^k, z - x^{k+1}⟫ ≥ 0` for all `z ∈ X`. -/
theorem optimality_65 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X) (f : NecoaraNG.Chain.E n → ℝ)
    (β L Lbar : ℝ) (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ z ∈ X,
      0 ≤ ⟪x (k + 1) - x k + α k • gradient f (x k) - e k, z - x (k + 1)⟫_ℝ := by sorry

end NecoaraNG.FDM
