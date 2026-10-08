-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_potential_step
-- name    : NesterovRCD.Accelerated.potential_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:04.849665+00:00
-- url     : https://prove2.me/theorems/2cd0f90d-bcc1-4232-8aaa-3ee74b6c7204
-- title:
--   Proof of Theorem 6, p. 16 — $2a_{k+1}^2(\phi_{k+1}-f^*)+b_{k+1}^2\mathbb E r_{k+1}^2\le 2a_k^2(\phi_k-f^*)+b_k^2\mathbb E r_k^2$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$, $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ blocks, each $\mathbb R^{n_i}$ carrying a Euclidean norm (3.4). Assume:
--
--   1. $f$ has a coordinate-wise Lipschitz gradient (2.2) with constants $L_i>0$;
--   2. $f$ is strongly convex (3.1) in the norm $\|\cdot\|_1$ of (3.5) with a parameter $\sigma$, $0\le\sigma<n^2$ ($\sigma=0$ meaning convexity);
--   3. $x_*$ is a minimizer of $f$, $f^*=f(x_*)$;
--   4. $s\mapsto s^\#$ is any selection of (1.8) on each block.
--
--   Run ACDM$(x_0)$ (5.1) with uniform draws, and let $\phi_k=\mathbb E_{\xi_{k-1}}f(x_k)$ and $\mathbb E_{\xi_{k-1}}(r_k^2)$ with $r_k=\|v_k-x_*\|_1$. Then for every $k\ge0$
--   $$2a_{k+1}^2(\phi_{k+1}-f^*)+b_{k+1}^2\,\mathbb E_{\xi_k}(r_{k+1}^2)\le 2a_k^2(\phi_k-f^*)+b_k^2\,\mathbb E_{\xi_{k-1}}(r_k^2),$$
--   and consequently, for every $k\ge0$,
--   $$2a_k^2(\phi_k-f^*)+b_k^2\,\mathbb E_{\xi_{k-1}}(r_k^2)\le 2a_0^2(f(x_0)-f^*)+b_0^2\|x_0-x_*\|_1^2.$$
--
--   This is the potential (Lyapunov) inequality of the accelerated method; with the growth of $a_k$ it gives the rate (5.3).
--
--   **Formalization Note** The paper writes $b_k^2r_k^2$ in the middle term right after taking the expectation in $\xi_{k-1}$; it is $b_k^2\,\mathbb E_{\xi_{k-1}}(r_k^2)$, and that is what is stated. The standing assumptions of §2 (convexity, a nonempty optimal set, $L_i>0$, $n\ge1$), the Euclidean block norms of §3 and $\sigma<n^2$ (implicit in (5.1), whose $\alpha_k$ divides by $n^2-\sigma$) are explicit hypotheses; $\sigma$ is any valid convexity parameter, not necessarily the largest. Blocks are inner-product spaces `E i` indexed by `Fin n`; the draws are explicit sequences, and $\phi_k$, $\mathbb E r_k^2$ are the finite averages `acdmPhi`, `acdmR2` over all $n^k$ sequences with weight $n^{-k}$. $a_0=1/n$, $b_0=2$ by definition.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 16, proof of Theorem 6, after "Taking now the expectation of both sides of this inequality in ξ_{k−1}"

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem potential_step {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n)
    (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) :
    (∀ k : ℕ,
      2 * acdmA n σ (k + 1) ^ 2 * (acdmPhi f L sharp σ x0 (k + 1) - f xs)
          + acdmB n σ (k + 1) ^ 2 * acdmR2 f L sharp σ x0 xs (k + 1)
        ≤ 2 * acdmA n σ k ^ 2 * (acdmPhi f L sharp σ x0 k - f xs)
          + acdmB n σ k ^ 2 * acdmR2 f L sharp σ x0 xs k) ∧
    (∀ k : ℕ,
      2 * acdmA n σ k ^ 2 * (acdmPhi f L sharp σ x0 k - f xs)
          + acdmB n σ k ^ 2 * acdmR2 f L sharp σ x0 xs k
        ≤ 2 * acdmA n σ 0 ^ 2 * (f x0 - f xs) + acdmB n σ 0 ^ 2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2) := by sorry

end NesterovRCD.Accelerated
