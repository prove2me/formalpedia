-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_capacity
-- name    : MultiwayGap2325.Main.Supplement.affine_capacity
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:54:24.41358+00:00
-- url     : https://prove2.me/theorems/7baec589-d940-4981-87e7-8d4dc03ccfd6
-- title:
--   Capacity inequality for the affine flows
-- statement:
--   For every $q\ge2$ and $T\in(1/2,1)$, the affine label flows satisfy equation (8). On a face $S$ of cardinality $r$, let $I\subset S$ be nonempty and proper and put $P_I=\sum_{s\in I}p_s^S$. The relevant label-flow differences over the three groups $I$, $S\setminus I$, and $\{*\}$ have total span $a_r$, while the crossing weight is
--
--   $$
--   \frac{|I|(r-|I|)a_r}{r-1}\ge a_r.
--   $$
--
--   Thus the absolute mixed flow through every such cut is bounded by its total edge weight.
--
--   **Formalization Note** The conclusion is precisely `Capacity (affineData q T)`, including all points of each closed cell and every pair of allowed labels.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, capacity paragraph and equation (8), p.23.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.23, capacity paragraph: equation (8) holds for the affine data. -/
theorem affine_capacity (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    Capacity (affineData q T) := by sorry
