-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_6
-- name    : LiuHelsenDesigns.OneD.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:21.910226+00:00
-- url     : https://prove2.me/theorems/fed032f7-a091-4d69-a016-f0c049c12173
-- title:
--   Lemma 6 — permutation-block Weingarten discrepancy
-- statement:
--   Let ξ be a qubit count and let $k\le\xi-1$. On permutation-sector stochastic Lagrangians, use the actual Clifford and Haar inverse Gram matrices. Then
--
--   $$
--   \sum_{T,S\in S_k}2^{\xi k}|Wg_C(T,S)-Wg_H(T,S)|\le k!\,2^{k-2\xi+3}.
--   $$
--
--   The estimate controls the complete permutation-sector contribution, rather than one matrix entry.
--
--   Differences from the source: none.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 17, Lemma 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_commutants

namespace LiuHelsenDesigns.OneD
theorem lemma_6 (ξ k : ℕ) (hrange : k + 1 ≤ ξ) :
    ∑ T : PermSector k, ∑ S : PermSector k,
      (2 : ℝ)^(ξ*k) * |wgC ξ k T.val S.val - wgH ξ k T S| ≤
        (k.factorial : ℝ) * (2 : ℝ) ^ ((k : ℤ) - 2*ξ + 3) := by sorry
end LiuHelsenDesigns.OneD
