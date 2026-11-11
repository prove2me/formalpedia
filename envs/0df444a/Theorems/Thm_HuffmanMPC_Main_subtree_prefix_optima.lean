-- Prove2me | Theorems.Thm_HuffmanMPC_Main_subtree_prefix_optima
-- name    : HuffmanMPC.Main.subtree_prefix_optima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:56.186197+00:00
-- url     : https://prove2.me/theorems/4cd5dde4-1a83-43a5-904f-2f70a3730e65
-- title:
--   Lemma 6.3 — one optimal tree whose depth-$h^*$ weights are the increments of $P$
-- statement:
--   Let $f_1\le\dots\le f_m$ be positive frequencies, $m\ge2$, and $h$ an optimal depth vector. Fix an integer depth $0\le h^*\le h_{\min}$ and let $q=2^{h^*}$. There is a coding tree with the given leaf depths (hence optimal) whose $q$ node weights at depth $h^*$, sorted as $w_1\le\dots\le w_q$, satisfy, for every $0\le r\le q$ simultaneously,
--   $$P(r)=\sum_{j=1}^r w_j,\qquad\text{hence}\qquad w_r=P(r)-P(r-1).$$
--
--   The node weights at depth $h^*$ can therefore be read off from the values $P(r)$ without building the tree.
--
--   Differences from the source:
--   - encoding: Section 6's standing input condition $f_m/f_2\le\lambda$ → omitted; reason: the conclusion does not involve $\lambda$, and every sorted positive list satisfies it with $\lambda=f_m/f_2$
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 6.3, p. 27 (PDF 28)

import Definitions.Def_HuffmanMPC_Main_Reconstruction

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem subtree_prefix_optima (a : Frequencies) (ha : Positive a)
    (hm : 2 ≤ a.length) (hs : a.Pairwise (· ≤ ·))
    (h : Fin a.length → ℕ) (hh : OptimalDepths a h)
    (star : ℕ) (hst : star ≤ minDepth h) :
    ∃ t : CodingTree a.length, t.HasDepths h ∧
      let w := (t.levelWeights star).mergeSort (· ≤ ·)
      w.length = 2^star ∧ ∀ r ≤ 2^star,
        prefixOptimum a h star r = ((w.take r).sum : ℕ∞) := by sorry

end HuffmanMPC.Main
