-- Prove2me | Theorems.Thm_HuffmanMPC_Main_budget_split_layered_convexity
-- name    : HuffmanMPC.Main.budget_split_layered_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:24.935832+00:00
-- url     : https://prove2.me/theorems/cfd2cf89-eea4-4b4e-ac28-21e092e86b81
-- title:
--   Lemma 5.4 — $G_b$ is layered convex modulo $2^{u-\ell-1}$
-- statement:
--   Let $A_1,A_2$ be lists of positive frequencies, $A=A_1\uplus A_2$, $1\le\ell<u$, and $b\in\mathcal B(A)$. Write $G_b(x)=\mu(A_1,x)+\mu(A_2,b-x)$ and $d=2^{u-\ell-1}$. Whenever $x+2d\le b$ and $G_b(x),G_b(x+d),G_b(x+2d)$ are finite,
--   $$G_b(x+2d)-G_b(x+d)\ \ge\ G_b(x+d)-G_b(x).$$
--
--   Layered convexity lets each budget's best split be found by searching every residue class separately.
--
--   Differences from the source:
--   - generalization: $\ell,u$ of the bounded-ratio instance → any integers $1\le\ell<u$; reason: the proof uses only Eq. (6) and Lemma 5.3
--   - generalization: domain of $G_b$: the feasible divisions $x\in\mathcal B(A_1)$, $b-x\in\mathcal B(A_2)$ → every $x$ at which the three values are finite; reason: this contains the source's domain; on it, $\mu$ is given by Eq. (6) for every budget
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 5.4, p. 22 (PDF 23)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem budget_split_layered_convexity (a₁ a₂ : Frequencies)
    (ha₁ : Positive a₁) (ha₂ : Positive a₂) (lo hi b : ℕ)
    (hl : 1 ≤ lo) (hu : lo < hi) (hb : b ∈ relevantBudgets (a₁ ++ a₂) lo hi) :
    LayeredSplitConvex a₁ a₂ lo hi b (2^(hi-lo-1)) := by sorry

end HuffmanMPC.Main
