-- Prove2me | Theorems.Thm_ManPG_Conv_theorem_5_5
-- name    : ManPG.Conv.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:39.707587+00:00
-- url     : https://prove2.me/theorems/47371620-e64b-4b58-8da2-4a11ef140855
-- title:
--   Theorem 5.5 — limit points of ManPG are stationary; with t = 1/L an ε-stationary point within ⌈2L(F(X₀) − F*)/(γᾱε²)⌉ iterations
-- statement:
--   Consider problem (1.1),
--   $$\min_{X\in\mathcal M} F(X)=f(X)+h(X),\qquad \mathcal M=\mathrm{St}(n,r)=\{X\in\mathbb R^{n\times r}:X^\top X=I_r\},$$
--   under the standing assumptions: $r\le n$; $f$ is differentiable with $L$-Lipschitz gradient $\nabla f$ ($L>0$); $h$ is convex and $L_h$-Lipschitz; all norms are Frobenius norms. Let $\mathrm{Retr}$ be a retraction on $\mathcal M$ with constants $M_1,M_2>0$ in (3.1)–(3.2), and let $G>0$ satisfy $\|\nabla f(X)\|_F\le G$ on $\mathcal M$. Let $\gamma\in(0,1)$, $t>0$, and let $(X_k),(V_k),(\alpha_k)$ be a run of Algorithm 1 (ManPG) with these parameters. Then:
--
--   1. Every limit point $\bar X$ of $\{X_k\}$ is a stationary point of (1.1) (Definition 3.3).
--   2. If $t=1/L$, then for every $\varepsilon>0$ some iteration
--   $$k\le\left\lceil\frac{2L\,(F(X_0)-F^*)}{\gamma\bar\alpha\varepsilon^2}\right\rceil,\qquad \bar\alpha=\frac1{2(c_0+L_hM_2)t},\quad c_0=M_2G+\frac{LM_1^2}2,$$
--   satisfies the stopping test $\|V_k\|_F\le\varepsilon/L$, and $X_k$ is an $\varepsilon$-stationary point of (1.1) (Definition 5.4). Here $F^*$ is the optimal value of (1.1).
--
--   This is the main convergence result for ManPG. It gives global convergence to stationary points and an $O(\varepsilon^{-2})$ iteration complexity. The iteration complexity matches that of Riemannian gradient descent for smooth problems.
--
--   **Formalization Note**
--   - "Limit point" means cluster point of the sequence (`MapClusterPt`) in the usual topology of $\mathbb R^{n\times r}$.
--   - "Returns an $\varepsilon$-stationary point within $N$ iterations" means that some $k\le N$ passes the paper's stopping test $\|V_k\|_F\le\varepsilon/L$ and that $X_k$ is $\varepsilon$-stationary. The non-strict $k\le N$ covers $F(X_0)=F^*$, where $N=0$.
--   - $F^*$ is any attained lower bound of $F$ on $\mathcal M$.
--   - The first claim holds for every $t>0$; only the second fixes $t=1/L$.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 13, Theorem 5.5

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Theorem 5.5, p. 13: every limit point of the iterates `{X_k}` of Algorithm 1 is a stationary
point of (1.1); moreover, with `t = 1/L`, Algorithm 1 returns an `ε`-stationary point within
`⌈2L(F(X₀) − F*)/(γᾱε²)⌉` iterations, where `ᾱ = 1/(2(c₀ + L_h M₂)t)` (Lemma 5.2) and `F*` is the
optimal value of (1.1): some `k ≤ ⌈…⌉` has `‖V_k‖_F ≤ ε/L` (the stopping test) and `X_k` is
`ε`-stationary (Definition 5.4). -/
theorem theorem_5_5 {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    (X V : ℕ → Mat n r) (α : ℕ → ℝ) (hrun : IsManPGRun f gradf h R γ t X V α) :
    (∀ Xbar : Mat n r, MapClusterPt Xbar atTop X → IsStationary gradf h Xbar) ∧
    (t = 1 / L → ∀ ε : ℝ, 0 < ε → ∀ Fstar : ℝ, IsOptimalValue f h Fstar →
      ∃ k : ℕ, k ≤ ⌈2 * L * (f (X 0) + h (X 0) - Fstar) / (γ * abar L Lh M1 M2 G t * ε ^ 2)⌉₊ ∧
        frobNorm (V k) ≤ ε / L ∧ IsEpsStationary gradf h L ε (X k)) := by sorry

end ManPG.Conv
