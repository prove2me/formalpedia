-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_7
-- name    : HighMagSampling.SK.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:28:48.666408+00:00
-- url     : https://prove2.me/theorems/ecd1b093-4879-4891-9b6f-11d335bc36b2
-- title:
--   Lemma 7 — the random walk with weights $a_ia_j e^{K_{ij}}$ has $\lambda_2(P)\le e^{m(K)}\rho(K)$
-- statement:
--   Let $a\in\mathbb R^d_{>0}$ and let $K\in\mathbb R^{d\times d}$ be symmetric with $K_{ii}=0$ for all $i$. Define the edge weights
--   $$W_{ij}=\begin{cases}a_ia_j\exp(K_{ij}) & i\ne j,\\ 0 & i=j,\end{cases}$$
--   and let $P=D^{-1}W$ be the associated random walk matrix. With $m(K)=\max_{i,j}|K_{ij}|$, $X_{ij}=\exp(K_{ij})-1$ and $\rho(K)=\max\big(0,\sup_{\mathrm{nnz}(u)>1}\frac{u^\top(X-I_d)u}{\|u\|_1^2-\|u\|_2^2}\big)$,
--   $$\lambda_2(P)\ \le\ \exp(m(K))\,\rho(K).$$
--
--   The unperturbed case $K=0$ is a rank-one matrix with its diagonal removed, whose walk has $\lambda_2\le0$; the lemma makes this robust, and it is what Lemma 8 applies to each link graph of the Ising measure.
--
--   **Formalization Note.** $\lambda_2(P)$ is `lambdaTwoRW W`, the second eigenvalue with multiplicity of $D^{-1/2}WD^{-1/2}$, which is similar to $P$ since every degree is positive.
--
--   Differences from the source:
--   - encoding: $d$ unrestricted → $d\ge2$; reason: for $d=1$ the weight matrix is $0$, so $D=0$ and $P=D^{-1}W$ is undefined; this only excludes the undefined case.
--   - encoding: $\lambda_2(P)$ → $\lambda_2$ with multiplicity of $D^{-1/2}WD^{-1/2}$; reason: the similar symmetric matrix the paper itself uses ("$\lambda_2(P)=\lambda_2(N)$").
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 20, Lemma 7, Eqs. (20)–(21)

import Mathlib
import Definitions.Def_HighMagSampling_SK_Spectral

namespace HighMagSampling.SK

/-- Lemma 7, p. 20: for `a ∈ ℝ^d_{>0}` and symmetric `K` with zero diagonal, the random walk of
the weights `W_ij = a_i a_j exp(K_ij)` (`i ≠ j`), `W_ii = 0`, has `λ₂(P) ≤ exp(m(K)) ρ(K)`. -/
theorem lemma_7 (d : ℕ) (hd : 2 ≤ d) (a : Fin d → ℝ) (ha : ∀ i, 0 < a i)
    (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) (hdiag : ∀ i, K i i = 0) :
    lambdaTwoRW (Matrix.of fun i j => if i = j then 0 else a i * a j * Real.exp (K i j)) ≤
      Real.exp (maxAbs K) * rho K := by sorry

end HighMagSampling.SK
