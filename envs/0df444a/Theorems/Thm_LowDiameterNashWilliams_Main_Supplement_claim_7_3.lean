-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_7_3
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:43:34.828061+00:00
-- url     : https://prove2.me/theorems/e3a0b00c-3296-4f45-9497-c8ca582181c8
-- title:
--   Claim 7.3 (used in the proof of Theorem 7) — Every tree bounds cover optimum
-- statement:
--   Let $k\ge2$, $D=2k$, and let a valid indexed Set Cover instance satisfy $|U|\le m$ and minimum frequency at least $D$. Let $G$ be its exact reduction graph and let $\tau$ be the minimum input cover size. Every spanning tree $T$ of $G$ satisfies
--   $$|\operatorname{int}(T)|\ge\tau.$$
--   The quantifier ranges over every spanning tree, whether or not it belongs to a chosen packing. This is the cover lower bound used on the NO side.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - generalization: k is sufficiently large in the surrounding hardness proof → every k at least 2 for the identical reduction graph and input conditions; reason: these three structural claims need only k at least 2; the proof inequalities and clique constructions remain valid
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 7.3, p. 30 (PDF p. 31)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_CoverGraph

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_7_3 (k : ℕ) (hk : 2 ≤ k) (I : SCInstance) (hI : FrequentCover I (2*k)) :
    let G := coverGraph I k
    ∀ T : Edges G.m, IsSpanningTree G.ends T → coverNumber I ≤ (internal G.ends T).card := by sorry

end LowDiameterNashWilliams.Main.Supplement
