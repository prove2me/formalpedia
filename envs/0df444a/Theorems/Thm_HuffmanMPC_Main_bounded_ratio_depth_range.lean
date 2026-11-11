-- Prove2me | Theorems.Thm_HuffmanMPC_Main_bounded_ratio_depth_range
-- name    : HuffmanMPC.Main.bounded_ratio_depth_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:05.213192+00:00
-- url     : https://prove2.me/theorems/cbac23aa-ed5b-4fff-97bd-aea643a99932
-- title:
--   Corollary 4.2 — an optimal tree with all depths in $[\ell,u]$
-- statement:
--   Let $f_1\le\dots\le f_m$ be positive frequencies, $m\ge2$, with $f_m\le\lambda f_2$. With $\Delta_\lambda=\lceil\log_\varphi\lambda\rceil+1$,
--   $$\ell=\max\{1,\lceil\log_2 m\rceil-\Delta_\lambda\},\qquad u=\lfloor\log_2 m\rfloor+\Delta_\lambda,$$
--   there is an optimal depth vector (an optimal tree) whose depths all lie in $[\ell,u]$.
--
--   This restricts every depth to a window of width at most $2\Delta_\lambda$ and turns the Kraft inequality into an integer budget of $2^u$ units.
--
--   Differences from the source:
--   - encoding: an optimal tree → a depth vector realized by a prefix-free code with cost $\mu$; reason: leaf depths of a coding tree are the codeword lengths
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Corollary 4.2, p. 14 (PDF 15)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem bounded_ratio_depth_range (a : Frequencies) (lam : ℝ)
    (ha : BoundedRatio a lam) :
    ∃ h : Fin a.length → ℕ, OptimalDepths a h ∧
      ∀ i, lowerDepth a.length lam ≤ h i ∧ h i ≤ upperDepth a.length lam := by sorry

end HuffmanMPC.Main
