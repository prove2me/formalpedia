-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_5_2
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:38:15.388531+00:00
-- url     : https://prove2.me/theorems/692f9bc8-c2fc-4a33-aecf-67af80ddfebf
-- title:
--   Claim 5.2 (used in the proof of Theorem 5) — Root depth iff extended diameter
-- statement:
--   Fix $k\ge2$, $\ell\ge1$, a finite simple rooted graph $(F,r)$ promised to have a $k$-tree packing, and any finite dummy set. Let $G$ be the exact tail extension at $r$. Then
--   $$F\text{ has a }k\text{-tree packing of root depth at most }2
--   \quad\Longleftrightarrow\quad
--   G\text{ has a }k\text{-tree packing with each diameter at most }3\ell+2.$$
--   Both directions are included, with no extra edges or tree certificate supplied. This is the conversion between the rooted decision problem and the diameter threshold.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: any finite dummy set in the first tail block → a natural dummy count and fixed numeric labels in the exact constructed graph; reason: finite relabelling changes no instance; all block and terminal adjacencies are prescribed
--   - encoding: shortest-path lengths, rooted depth and diameter measured in edges → published extended nonnegative distances, with depth and diameter taken by finite suprema; reason: on the connected graphs and spanning trees in these statements these values are the finite source values; disconnected pairs have infinite distance
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 5.2, p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Tail
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Promises

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open SetCoverThreshold.SetCover

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_5_2 (k ell d : ℕ) (hk : 2 ≤ k) (hell : 1 ≤ ell)
    (F : GraphInput) (r : Fin F.n) (hF : SimplePackingPromise k F) :
    HasDepthPacking F k r 2 ↔ HasDiameterPacking (tailExtension F r k ell d) k (3 * ell + 2 : ℕ) := by sorry

end LowDiameterNashWilliams.Main.Supplement
