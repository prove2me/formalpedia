-- Prove2me | Theorems.Thm_NesterovRCD_Constrained_theorem5
-- name    : NesterovRCD.Constrained.theorem5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:56.282545+00:00
-- url     : https://prove2.me/theorems/375da3aa-4ecb-4cfd-b533-64fb8bf864ee
-- title:
--   Theorem 5 — UCDM on $\min_{x\in Q}f$: $\varphi_k-f^*\le\frac n{n+k}\big[\frac12R_1^2(x_0)+f(x_0)-f^*\big]$, linear rate (4.6) under strong convexity
-- statement:
--   Consider the constrained problem (4.1), $\min_{x\in Q}f(x)$, where:
--
--   1. $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ and every $n_i\ge1$, each block carrying a Euclidean norm $\|h\|_{(i)}^2=\langle B_ih,h\rangle$ (3.4), and $\|h\|_1^2=\sum_iL_i\|h^{(i)}\|_{(i)}^2$ (3.5);
--   2. $Q=Q_1\times\cdots\times Q_n$ with each $Q_i\subseteq\mathbb R^{n_i}$ nonempty, closed and convex;
--   3. $f:\mathbb R^N\to\mathbb R$ is convex and has a coordinate-wise Lipschitz gradient (2.2) with constants $L_i>0$;
--   4. $x_*$ is an optimal solution of (4.1), $f^*=f(x_*)$, the starting point satisfies $x_0\in Q$, and $R\ge R_1(x_0)$, i.e. $\|x-x_*'\|_1\le R$ for every $x\in Q$ with $f(x)\le f(x_0)$ and every optimal solution $x_*'$.
--
--   Run the uniform coordinate descent method UCDM$(x_0)$ (4.5): at each step $k\ge0$ draw $i_k$ uniformly from $\{1,\dots,n\}$ and set $x_{k+1}=V_{i_k}(x_k)$, with $V_i$ the constrained coordinate update (4.2). Let $\varphi_k=\mathbb E_{\xi_{k-1}}f(x_k)$ be the expected objective after $k$ steps. Then for every $k\ge0$,
--   $$\varphi_k-f^*\le\frac n{n+k}\Big[\tfrac12R^2+f(x_0)-f^*\Big].$$
--   If moreover $f$ is strongly convex in $\|\cdot\|_1$ with constant $\sigma>0$ (3.1), then for every $k\ge0$,
--   $$\varphi_k-f^*\le\Big(1-\frac{2\sigma}{n(1+\sigma)}\Big)^k\Big(\tfrac12R^2+f(x_0)-f^*\Big).\qquad(4.6)$$
--
--   This is the main result of §4: the randomized block method extends to separable (block-product) constraints with the same $O(n/k)$ rate as in the unconstrained case, and with a linear rate under strong convexity, without any knowledge of $\sigma$.
--
--   **Formalization Note** The paper states the bounds with $R_1(x_0)$; Lean takes any upper bound $R$ of it, which is equivalent when $R_1(x_0)$ is finite and avoids the junk value of a supremum. $R_1(x_0)$ is read for problem (4.1): the level set is taken inside $Q$ and $X_*$ is the set of optimal solutions of (4.1). The paper leaves implicit that $x_0\in Q$ (UCDM changes one block at a time, so its iterates are feasible only if $x_0$ is) and that the $Q_i$ are nonempty; both are stated, as are $n\ge1$ and $n_i\ge1$ (nontrivial blocks; without them the factor in (4.6) could be negative, see footnote 2). Both bounds form one theorem of the paper and are stated as a conjunction; the second carries its own hypotheses $\sigma>0$ and strong convexity, and $\sigma\le1$ is not assumed (it follows from (2.2), footnote 2). The draws are explicit index sequences and $\varphi_k$ is the finite average of $f(x_k)$ over all $n^k$ sequences. The update $u^{(i)}(x)$ is a `Classical.epsilon` choice, equal to the paper's unique minimizer under these hypotheses. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 13, Theorem 5, (4.6)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem theorem5 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) [∀ i, Nontrivial (E i)]
    (x0 : NesterovRCD.Sublinear.Blocks E) (hx0 : x0 ∈ Qset Q) (xs : NesterovRCD.Sublinear.Blocks E) (hxs : IsMinimizerOn f Q xs)
    (R : ℝ) (hR : LevelRadiusOnLE f L Q x0 R) :
    (∀ k : ℕ, NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
        ≤ (n : ℝ) / ((n : ℝ) + k) * (R ^ 2 / 2 + f x0 - f xs)) ∧
    (∀ σ : ℝ, 0 < σ → NesterovRCD.HighProb.StronglyConvexW f L 1 σ → ∀ k : ℕ,
        NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
          ≤ (1 - 2 * σ / ((n : ℝ) * (1 + σ))) ^ k * (R ^ 2 / 2 + f x0 - f xs)) := by sorry

end NesterovRCD.Constrained
