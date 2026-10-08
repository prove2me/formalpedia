-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_theorem6
-- name    : NesterovRCD.Accelerated.theorem6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:54.063476+00:00
-- url     : https://prove2.me/theorems/0f443ff4-1bca-4e93-8149-561518a46ea1
-- title:
--   Theorem 6 (5.3) — ACDM: $\phi_k-f^*\le\big(\frac n{k+1}\big)^2\big[2\|x_0-x^*\|_1^2+\frac1{n^2}(f(x_0)-f^*)\big]$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$, $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ blocks, each $\mathbb R^{n_i}$ carrying a Euclidean norm (3.4), and let $\|\cdot\|_1$ be the norm (3.5), $\|x\|_1^2=\sum_iL_i\|x^{(i)}\|_{(i)}^2$. Assume:
--
--   1. $f$ has a coordinate-wise Lipschitz gradient (2.2) with constants $L_i>0$;
--   2. $f$ is strongly convex (3.1) in $\|\cdot\|_1$ with a known parameter $\sigma$, $0\le\sigma<n^2$ ($\sigma=0$ meaning convexity);
--   3. $x^*$ is a minimizer of $f$ and $f^*=f(x^*)$;
--   4. $s\mapsto s^\#$ is any selection of (1.8) on each block.
--
--   Let ACDM$(x_0)$ (5.1) run with independent uniform draws, $\phi_k=\mathbb E_{\xi_{k-1}}f(x_k)$, and
--   $$D=2\|x_0-x^*\|_1^2+\frac1{n^2}\big(f(x_0)-f^*\big).$$
--   Then for every $k\ge0$:
--
--   1. if $\sigma>0$,
--   $$\phi_k-f^*\le\sigma D\cdot\Big[\Big(1+\frac{\sqrt\sigma}{2n}\Big)^{k+1}-\Big(1-\frac{\sqrt\sigma}{2n}\Big)^{k+1}\Big]^{-2}\le\Big(\frac n{k+1}\Big)^2D;$$
--   2. in all cases ($\sigma\ge0$),
--   $$\phi_k-f^*\le\Big(\frac n{k+1}\Big)^2D.$$
--
--   The accelerated scheme thus improves the $O(n/k)$ expected rate of the plain random coordinate descent method to $O(n^2/k^2)$, and for $\sigma>0$ the first bound decreases geometrically, asymptotically by the factor $(1+\sqrt\sigma/(2n))^{-2}$ per iteration.
--
--   **Formalization Note** The paper states (5.3) as one chain for every $\sigma\ge0$. At $\sigma=0$ the middle expression is $0\cdot[0]^{-2}$, which the paper reads as its limit $(n/(k+1))^2D$, while Lean evaluates it to $0$; so the chain is stated for $\sigma>0$, and the outer bound separately for all $\sigma\ge0$. The standing assumptions of §2 (convexity, a nonempty optimal set, $L_i>0$, $n\ge1$), the Euclidean block norms and $\sigma<n^2$ (implicit in (5.1), whose $\alpha_k$ divides by $n^2-\sigma$) are explicit hypotheses; $\sigma$ is any valid convexity parameter. Blocks are inner-product spaces `E i` indexed by `Fin n`; the draws are explicit sequences and $\phi_k$ is the finite average `acdmPhi` over all $n^k$ draw sequences with weight $n^{-k}$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 15, Theorem 6, (5.3)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem theorem6 {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n)
    (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) (k : ℕ) :
    (0 < σ →
      acdmPhi f L sharp σ x0 k - f xs
        ≤ σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2 ∧
      σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2
        ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))) ∧
    acdmPhi f L sharp σ x0 k - f xs
      ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs)) := by sorry

end NesterovRCD.Accelerated
