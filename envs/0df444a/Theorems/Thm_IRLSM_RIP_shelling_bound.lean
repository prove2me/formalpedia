-- Prove2me | Theorems.Thm_IRLSM_RIP_shelling_bound
-- name    : IRLSM.RIP.shelling_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:03.549368+00:00
-- url     : https://prove2.me/theorems/33217844-c429-42f8-b8d8-7dde5341f167
-- title:
--   Proof of Proposition 6.8, p. 19 — shelling bound ‖σ^(j+1)‖₂ ≤ ℓ^(−1/2)‖σ^(j)‖₁ for a nonincreasing sequence
-- statement:
--   Let $s_0 \ge s_1 \ge s_2 \ge \cdots \ge 0$ be a nonincreasing sequence of nonnegative reals and let $\ell \ge 1$ be an integer. Cut the indices into consecutive blocks of length $\ell$. Each block has Euclidean norm at most $\ell^{-1/2}$ times the $\ell_1$ norm of the block before it: for every $j \ge 0$,
--   $$
--   \Bigl(\sum_{i=(j+1)\ell}^{(j+2)\ell-1} s_i^2\Bigr)^{1/2} \le \frac{1}{\sqrt\ell}\sum_{i=j\ell}^{(j+1)\ell-1} s_i .
--   $$
--
--   In the proof of Proposition 6.8 the sequence is the vector $\tilde\sigma$ of singular values of $\hat H_{22}$, the blocks are the vectors $\sigma^{(j)}$, and the bound reads $\|H_{j+1}\|_F \le \ell^{-1/2}\|H_j\|_*$. Summed over $j$, it controls the tail of $H_c$ in display (6.7).
--
--   **Formalization Note.** Indices are 0-based, so the block $\{j\ell,\dots,(j+1)\ell-1\}$ is the paper's $\sigma^{(j+1)}$. The paper states the bound "for $j \ge 2$"; (6.7) uses it for every block, and it holds for every block for the same reason, so it is stated for all $j$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Proposition 6.8, p. 19, last display

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- The shelling bound: if `s` is a nonincreasing nonnegative sequence and the indices are
split into consecutive blocks of length `ℓ > 0`, the Euclidean norm of each block is at most
`ℓ^{-1/2}` times the `ℓ₁` norm of the block before it:
`(∑_{i=(j+1)ℓ}^{(j+2)ℓ-1} s_i²)^{1/2} ≤ ℓ^{-1/2} ∑_{i=jℓ}^{(j+1)ℓ-1} s_i`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Proposition 6.8, p. 19 (the bound
`‖H_{j+1}‖_F ≤ ℓ^{-1/2}‖H_j‖_*`, in its vector form: the singular values of `H_j` are the entries
of `σ^{(j)}`).

Formalization Notes: 0-based indices, so the block `Ico (jℓ) ((j+1)ℓ)` is the vector `σ^{(j+1)}`
of the page. The page says "for j ≥ 2"; the same argument holds, and display (6.7) uses it, for
every block, so it is stated for every `j : ℕ`. -/
theorem shelling_bound (s : ℕ → ℝ) (hs : Antitone s) (h0 : ∀ i, 0 ≤ s i) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (j : ℕ) :
    Real.sqrt (∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ^ 2) ≤
      (1 / Real.sqrt ℓ) * ∑ i ∈ Finset.Ico (j * ℓ) ((j + 1) * ℓ), s i := by sorry

end IRLSM.RIP
