-- Prove2me | Theorems.Thm_HuffmanMPC_Main_optimal_depth_difference
-- name    : HuffmanMPC.Main.optimal_depth_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:13.48764+00:00
-- url     : https://prove2.me/theorems/f8457e16-4b97-4309-9ed2-8fc0c5364cca
-- title:
--   Lemma 4.1 — depth difference bounded by $\lceil\log_\varphi(f_j/f_i)\rceil+1$
-- statement:
--   Let $f_1,\dots,f_m$ be positive frequencies with $m\ge2$, and let $(h_1,\dots,h_m)$ be any optimal depth assignment: the lengths of some prefix-free code whose cost $\sum_i f_ih_i$ equals $\mu$. Then for all $i,j$ with $f_i\le f_j$,
--   $$h_i-h_j\ \le\ \Big\lceil\log_\varphi\frac{f_j}{f_i}\Big\rceil+1,\qquad \varphi=\frac{1+\sqrt5}{2}.$$
--
--   Frequencies on a leaf-to-root path grow at least like the Fibonacci numbers; this lemma turns a bounded frequency ratio into a bounded range of optimal depths (Corollary 4.2).
--
--   Differences from the source:
--   - encoding: optimal depth assignment of Eq. (1) → depths realized by a prefix-free code with cost $\mu$; reason: by the Kraft–McMillan theorem quoted on p. 3 these are the same depth vectors
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 4.1, p. 13 (PDF 14)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem optimal_depth_difference (a : Frequencies) (ha : Positive a)
    (hm : 2 ≤ a.length) (h : Fin a.length → ℕ) (hh : OptimalDepths a h)
    (i j : Fin a.length) (hij : a[i] ≤ a[j]) :
    (h i : ℤ) - h j ≤ ⌈Real.logb phi ((a[j] : ℝ) / (a[i] : ℝ))⌉ + 1 := by sorry

end HuffmanMPC.Main
