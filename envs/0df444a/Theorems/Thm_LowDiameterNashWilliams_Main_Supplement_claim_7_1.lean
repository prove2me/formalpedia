-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_7_1
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:42:15.528772+00:00
-- url     : https://prove2.me/theorems/0b62ea64-58a6-455d-9bd4-c4af0419bcdf
-- title:
--   Claim 7.1 (used in the proof of Theorem 7) — Minimum-degree ratio
-- statement:
--   Let $k\ge2$, $D=2k$, and let $(U,S_1,\ldots,S_m)$ be any valid Set Cover instance with $|U|\le m$ and frequency at least $D$ for every element. Form the precise two-clique reduction graph $G$ from Section 7.2, and put $b=m/D$ and $n=|V(G)|$. Then
--   $$b+1<\frac{n}{\delta(G)}\le3b.$$
--   The degree and graph order are computed from the constructed graph, not assumed. No YES or NO cover-size condition is imposed.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - generalization: k is sufficiently large in the surrounding hardness proof → every k at least 2 for the identical reduction graph and input conditions; reason: these three structural claims need only k at least 2; the proof inequalities and clique constructions remain valid
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 7.1, p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_CoverGraph

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_7_1 (k : ℕ) (hk : 2 ≤ k) (I : SCInstance) (hI : FrequentCover I (2*k)) :
    let G := coverGraph I k
    let b : ℝ := (I.sets.length : ℝ) / (2*k)
    b + 1 < (G.n : ℝ) / minDegree G.ends ∧ (G.n : ℝ) / minDegree G.ends ≤ 3*b := by sorry

end LowDiameterNashWilliams.Main.Supplement
