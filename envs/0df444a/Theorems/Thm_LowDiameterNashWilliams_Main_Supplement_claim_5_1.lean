-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_5_1
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:37:36.555394+00:00
-- url     : https://prove2.me/theorems/0c9213ca-4af1-4818-87bb-9f6e5b024188
-- title:
--   Claim 5.1 (used in the proof of Theorem 5) — Tail distance and tree diameters
-- statement:
--   Let $k\ge2$, $\ell\ge1$, and let $H$ be the tail of $\ell$ blocks defined before the claim, with any finite dummy set in the first block and extreme terminals $s,t$. Then
--   $$\operatorname{dist}_H(s,t)=3\ell,$$
--   and there exist $k$ pairwise edge-disjoint spanning trees $T_i$ of $H$ satisfying
--   $$\operatorname{dist}_{T_i}(s,t)=\operatorname{diam}(T_i)=3\ell\qquad(i\in[k]).$$
--   The two equalities concern each tree of the same packing and hold before the padding choice in Theorem 5.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: any finite dummy set in the first tail block → a natural dummy count and fixed numeric labels in the exact constructed graph; reason: finite relabelling changes no instance; all block and terminal adjacencies are prescribed
--   - encoding: shortest-path lengths, rooted depth and diameter measured in edges → published extended nonnegative distances, with depth and diameter taken by finite suprema; reason: on the connected graphs and spanning trees in these statements these values are the finite source values; disconnected pairs have infinite distance
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 5.1, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Tail

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_5_1 (k ell d : ℕ) (hk : 2 ≤ k) (hell : 1 ≤ ell) :
    let H := tailGraph k ell d
    distance H.ends Finset.univ (tailStart k ell d) (tailEnd k ell d) = (3 * ell : ℕ) ∧
    ∃ T : Trees k H.m, Packing H.ends T ∧ ∀ i,
      distance H.ends (T i) (tailStart k ell d) (tailEnd k ell d) = (3 * ell : ℕ) ∧
      diameter H.ends (T i) = (3 * ell : ℕ) := by sorry

end LowDiameterNashWilliams.Main.Supplement
