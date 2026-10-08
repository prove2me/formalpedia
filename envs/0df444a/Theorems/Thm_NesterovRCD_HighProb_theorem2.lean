-- Prove2me | Theorems.Thm_NesterovRCD_HighProb_theorem2
-- name    : NesterovRCD.HighProb.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:41.950974+00:00
-- url     : https://prove2.me/theorems/c0f318fb-0917-4b4f-8d50-10d9a077e726
-- title:
--   Theorem 2, (3.3) — RCDM$(\alpha,x_0)$ on a $\sigma$-strongly convex $f$: $\phi_k-f^*\le(1-\sigma/S_\alpha)^k(f(x_0)-f^*)$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$, $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ blocks carrying arbitrary norms $\|\cdot\|_{(i)}$, have a coordinate-wise Lipschitz gradient with constants $L_i>0$ (2.2). Let $\alpha\in\mathbb R$ and suppose $f$ is strongly convex with respect to the norm $\|x\|_{1-\alpha}=\big[\sum_iL_i^{1-\alpha}\|x^{(i)}\|_{(i)}^2\big]^{1/2}$ with convexity parameter $\sigma>0$:
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\tfrac12\sigma\|y-x\|_{1-\alpha}^2\quad\text{for all }x,y.$$
--   Let $x_*$ be a minimizer of $f$, $f^*=f(x_*)$, and $S_\alpha=\sum_iL_i^\alpha$. Run RCDM$(\alpha,x_0)$: at each step draw block $i$ with probability $L_i^\alpha/S_\alpha$, independently, and set $x_{k+1}=T_{i_k}(x_k)=x_k-\frac1{L_{i_k}}U_{i_k}f'_{i_k}(x_k)^\#$, with any choice of the vectors $s^\#$ of (1.8). Then for every $k\ge0$ the expected value $\phi_k=\mathbb E\,f(x_k)$ over the first $k$ draws satisfies
--   $$\phi_k-f^*\le\Big(1-\frac{\sigma}{S_\alpha}\Big)^k\big(f(x_0)-f^*\big).$$
--
--   This is the linear convergence rate of random block coordinate descent under strong convexity; Lemma 4 and Theorem 4 apply it to the regularized objective $f_\mu$ with $\alpha=1$.
--
--   **Formalization Note** The paper prints the left side as $\phi_k-\phi^*$; its proof ends with $f(x_k)-f^*$ and "it remains to compute the expectation", so the left side is $\phi_k-f^*$, as stated here. The block norms are arbitrary (Theorem 2 precedes the Euclidean assumption (3.4)). The paper's standing assumptions of §2 are explicit: $n\ge1$, $L_i>0$ (inside `CoordLipschitz`), the existence of a minimizer. Convexity of $f$ follows from (3.1) and is not a separate hypothesis. Blocks are `Fin n`, 0-based; the expectation is the finite sum `expect (prob L α) k` over all draw sequences `Fin k → Fin n`; the $s^\#$ are an arbitrary selection satisfying (1.8).
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 9, Theorem 2, (3.3)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic

namespace NesterovRCD.HighProb

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem theorem2 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (α σ : ℝ) (hσ : 0 < σ) (hsc : StronglyConvexW f L (1 - α) σ)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) (k : ℕ) :
    NesterovRCD.Sublinear.expect (NesterovRCD.Sublinear.prob L α) k (fun idx => f (NesterovRCD.Sublinear.rcdm f L sharp x0 k idx)) - f xs
      ≤ (1 - σ / NesterovRCD.Sublinear.S L α) ^ k * (f x0 - f xs) := by sorry

end NesterovRCD.HighProb
