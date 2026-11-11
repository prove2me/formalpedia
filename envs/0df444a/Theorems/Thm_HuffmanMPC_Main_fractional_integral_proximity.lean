-- Prove2me | Theorems.Thm_HuffmanMPC_Main_fractional_integral_proximity
-- name    : HuffmanMPC.Main.fractional_integral_proximity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:27.594732+00:00
-- url     : https://prove2.me/theorems/ab25a4db-660c-472c-956b-27dc8d0b35dc
-- title:
--   Lemma 6.4 — some optimal selection differs from the greedy prefix in at most $2^{\Delta+1}-2$ leaves
-- statement:
--   Let $f_1\le\dots\le f_m$ be positive frequencies, $m\ge2$, $h$ an optimal depth vector, $\Delta=h_{\max}-h_{\min}$, $0\le h^*\le h_{\min}$ and $r\in\{0,\dots,2^{h^*}\}$. Fix any density order (nondecreasing $f_i/2^{-h_i}$, any tie order) and let $R$ be the set of leaves the fractional greedy selects completely for the target $r2^{-h^*}$. There is a set of leaves $S$ attaining $P(r)$, i.e. $\sum_{i\in S}2^{-h_i}=r2^{-h^*}$ and $\sum_{i\in S}f_i=P(r)$, with
--   $$|R\,\triangle\,S|\ \le\ 2^{\Delta+1}-2.$$
--
--   This bound localizes the exact problems for $P(r)$ to small windows around the greedy cutoffs.
--
--   Differences from the source:
--   - encoding: Section 6's standing input condition $f_m/f_2\le\lambda$ → omitted; reason: the conclusion does not involve $\lambda$, and every sorted positive list satisfies it with $\lambda=f_m/f_2$
--   - encoding: the fractional greedy with one fixed tie order → every density order; reason: each fixed tie order is one such order
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 6.4, p. 28 (PDF 29)

import Definitions.Def_HuffmanMPC_Main_Reconstruction

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Lemma 6.4 (p. 28), for every density order of the fractional greedy. -/
theorem fractional_integral_proximity (a : Frequencies) (ha : Positive a)
    (hm : 2 ≤ a.length) (hs : a.Pairwise (· ≤ ·))
    (h : Fin a.length → ℕ) (hh : OptimalDepths a h)
    (star r : ℕ) (hst : star ≤ minDepth h) (hr : r ≤ 2 ^ star)
    (order : List (Fin a.length)) (hord : IsDensityOrder a h order) :
    ∃ s : Finset (Fin a.length),
      selectedKraft h s = r * kraft star ∧
      prefixOptimum a h star r = (selectedCost a s : ℕ∞) ∧
      (((greedyComplete h order star r) \ s) ∪ (s \ greedyComplete h order star r)).card ≤
        2 ^ (maxDepth h - minDepth h + 1) - 2 := by sorry

end HuffmanMPC.Main
