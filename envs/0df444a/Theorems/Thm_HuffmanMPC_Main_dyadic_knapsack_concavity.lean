-- Prove2me | Theorems.Thm_HuffmanMPC_Main_dyadic_knapsack_concavity
-- name    : HuffmanMPC.Main.dyadic_knapsack_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:26.976983+00:00
-- url     : https://prove2.me/theorems/b492f6ae-9b7f-4666-954b-120a9937e954
-- title:
--   Lemma 5.3 — the dyadic knapsack optimum is concave on residue classes modulo $2^{u-\ell-1}$
-- statement:
--   Let $A$ be a list of positive frequencies and $1\le\ell<u$. For each occurrence $f_i$ create items of sizes $1,2,\dots,2^{u-\ell-1}$, each of value $f_i$, and let $\psi(A,c)$ be the maximum value of items of total size at most $c$. Set $d=2^{u-\ell-1}$. For every $r\in\{0,\dots,d-1\}$ the sequence $\psi(A,r),\psi(A,r+d),\psi(A,r+2d),\dots$ is concave:
--   $$\psi(A,r+(k+2)d)-\psi(A,r+(k+1)d)\ \le\ \psi(A,r+(k+1)d)-\psi(A,r+kd)\qquad(k\ge0).$$
--
--   Through Eq. (6) this gives convexity of $\mu(A,\cdot)$ on each residue class, the basis of the fast merging step.
--
--   Differences from the source:
--   - generalization: $\ell,u$ of the bounded-ratio instance → any integers $1\le\ell<u$; reason: the statement and its proof do not depend on how $\ell,u$ were chosen
--   - encoding: $d=2^{u-\ell-1}$ for the instance's $\ell,u$ → hypothesis $\ell<u$; reason: only then is $d$ a positive integer; the paper's choices give $u>\ell$
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 5.3, p. 21 (PDF 22)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem dyadic_knapsack_concavity (a : Frequencies) (ha : Positive a)
    (lo hi : ℕ) (hl : 1 ≤ lo) (hu : lo < hi) :
    let d := 2^(hi-lo-1)
    ∀ r < d, ∀ k : ℕ,
      (knapsackOptimum a lo hi (r+(k+2)*d) : ℤ) -
          knapsackOptimum a lo hi (r+(k+1)*d) ≤
      (knapsackOptimum a lo hi (r+(k+1)*d) : ℤ) -
          knapsackOptimum a lo hi (r+k*d) := by sorry

end HuffmanMPC.Main
