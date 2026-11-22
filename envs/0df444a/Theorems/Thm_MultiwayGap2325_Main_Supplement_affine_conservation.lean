-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_conservation
-- name    : MultiwayGap2325.Main.Supplement.affine_conservation
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:57:01.605873+00:00
-- url     : https://prove2.me/theorems/bc3dda59-2fd9-4b39-80f6-45586f2bf6f1
-- title:
--   Conservation law for the affine flows
-- statement:
--   For every $q\ge2$ and $T\in(1/2,1)$, the affine label flows satisfy conservation (9). On a face of cardinality $r$, the tangent divergence of every terminal-label flow is
--
--   $$
--   \operatorname{div}F_i^S=\frac{(r-1)a_r}{rT-1}.
--   $$
--
--   For a child $U$ of cardinality $r<q$, each of its $q-r$ parents supplies $a_{r+1}T/((r+1)T-1)$, and the scale identity
--
--   $$
--   (q-r)a_{r+1}\frac{T}{(r+1)T-1}=\frac{(r-1)a_r}{rT-1}
--   $$
--
--   shows that divergence equals incoming supply, with zero allowance. On the top face there is no parent and its allowance $(q-1)a_q/(qT-1)$ equals the whole divergence. The star-label flow and both sides of its conservation equation vanish.
--
--   **Formalization Note** The target is the almost-everywhere statement `Conservation T (affineData q T)` with the chartwise divergence and incident-cell convention from `Flows`.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, conservation paragraphs and equation (9), pp.23–24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, pp.23–24: divergence equals parent supply plus allowance almost everywhere. -/
theorem affine_conservation (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    Conservation T (affineData q T) := by sorry
