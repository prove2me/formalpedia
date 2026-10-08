-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_theorem1
-- name    : NesterovRCD.Sublinear.theorem1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:49.736972+00:00
-- url     : https://prove2.me/theorems/9edbb442-fe25-4975-8425-449b68da9d84
-- title:
--   Theorem 1 — RCDM$(\alpha,x_0)$: $\varphi_k-f^*\le\frac2{k+4}\big[\sum_jL_j^\alpha\big]R^2_{1-\alpha}(x_0)$
-- statement:
--   Let $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ blocks, each carrying a norm $\|\cdot\|_{(i)}$. Let $f:\mathbb R^N\to\mathbb R$ be convex and differentiable, with coordinate-wise Lipschitz continuous gradient (2.2) with constants $L_1,\dots,L_n>0$, and let $x_*$ be a minimizer of $f$, $f^*=f(x_*)$. Fix $\alpha\in\mathbb R$ and a starting point $x_0$, and let $R\ge R_{1-\alpha}(x_0)$, where
--   $$R_\beta(x_0)=\max_x\Big\{\max_{x_*\in X_*}\|x-x_*\|_\beta:\ f(x)\le f(x_0)\Big\}.$$
--   Run the random coordinate descent method RCDM$(\alpha,x_0)$: at step $k$ draw $i_k$ independently with $\Pr(i_k=i)=L_i^\alpha/\sum_jL_j^\alpha$ and set $x_{k+1}=T_{i_k}(x_k)=x_k-\frac1{L_{i_k}}U_{i_k}f'_{i_k}(x_k)^\#$, where $s^\#$ is any vector of $\operatorname{Arg\,max}_x[\langle s,x\rangle-\frac12\|x\|^2]$. Then the expected value $\varphi_k=E_{\xi_{k-1}}f(x_k)$ satisfies, for every $k\ge0$,
--   $$\varphi_k-f^*\le\frac2{k+4}\cdot\Big[\sum_{j=1}^nL_j^\alpha\Big]\cdot R^2 .$$
--
--   This is the paper's first global efficiency estimate: random coordinate descent converges in expectation at the rate $O(1/k)$, with a constant governed by the sum $S_\alpha$ of powers of the coordinate Lipschitz constants rather than by the global Lipschitz constant. For $\alpha=0$ (uniform sampling) it gives $\frac{2n}{k+4}R_1^2(x_0)$, and for $\alpha=1$ it gives $\frac2{k+4}S_1R_0^2(x_0)$.
--
--   **Formalization Note** The paper states the bound with $R_{1-\alpha}(x_0)$ itself; we state it for every upper bound $R$ of $R_{1-\alpha}(x_0)$, which is equivalent whenever the max is finite (the paper assumes $X_*$ bounded) and avoids a junk value of a supremum. The standing assumptions of §2 (p. 4: $f$ convex and differentiable, $X_*$ nonempty) are hypotheses; $L_i>0$ and $n\ge1$ are implicit in the paper (the method divides by $L_i$ and samples from $\{1,\dots,n\}$) and stated explicitly. $\alpha$ ranges over all of $\mathbb R$ as in (2.5). The blocks are `Fin n` with 0-based indices, each a finite-dimensional real normed space; the dual norm is the operator norm; the choice of $s^\#$ is arbitrary (`IsSharpSelection`); $\varphi_k$ is the finite sum over all index sequences of length $k$ weighted by the product of their probabilities.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 7, Theorem 1, (2.12)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem theorem1 (hn : 0 < n) (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hR : LevelRadiusLE f L (1 - α) x0 R) (k : ℕ) :
    expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx)) - f xs
      ≤ 2 / ((k : ℝ) + 4) * S L α * R ^ 2 := by sorry

end NesterovRCD.Sublinear
