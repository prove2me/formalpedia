-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_7_2
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:42:50.840185+00:00
-- url     : https://prove2.me/theorems/2f0c9f8b-efb3-4cac-a92b-613b85d11f01
-- title:
--   Claim 7.2 (used in the proof of Theorem 7) — Covers give full tree packings
-- statement:
--   Let $k\ge2$, $D=2k$, and let a valid indexed Set Cover instance satisfy $|U|\le m$ and minimum element frequency at least $D$. For every cover $J$, its exact reduction graph $G$ admits one family of $k$ pairwise edge-disjoint spanning trees such that
--   $$|\operatorname{int}(T_i)|\le |J|+4\qquad(i\in[k]).$$
--   The conclusion holds for every cover, including all set indices; the graph need not be a YES instance of the hardness gap. It supplies the packing promise on both sides of the reduction.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - generalization: k is sufficiently large in the surrounding hardness proof → every k at least 2 for the identical reduction graph and input conditions; reason: these three structural claims need only k at least 2; the proof inequalities and clique constructions remain valid
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 7.2, p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_CoverGraph

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_7_2 (k : ℕ) (hk : 2 ≤ k) (I : SCInstance) (hI : FrequentCover I (2*k))
    (J : Finset (Fin I.sets.length)) (hJ : I.IsCover J) :
    let G := coverGraph I k
    ∃ T : Trees k G.m, Packing G.ends T ∧
      ∀ i, (internal G.ends (T i)).card ≤ J.card + 4 := by sorry

end LowDiameterNashWilliams.Main.Supplement
