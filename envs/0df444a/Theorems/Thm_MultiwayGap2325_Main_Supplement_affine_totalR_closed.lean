-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalR_closed
-- name    : MultiwayGap2325.Main.Supplement.affine_totalR_closed
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:00:32.334803+00:00
-- url     : https://prove2.me/theorems/0e23d4c2-b022-410e-a281-4d9453c5c518
-- title:
--   Integrated allowance of the affine flow instance
-- statement:
--   For the affine data with $q\ge2$ and $T\in(1/2,1)$, the integrated total allowance is
--
--   $$
--   R=\frac{1-q(1-T)^{q-1}}{q!\,T^{q-2}}.
--   $$
--
--   Only the top face has nonzero allowance. Its constant density is $(q-1)a_q/(qT-1)$, and its truncated-simplex volume is $(1-q(1-T)^{q-1})/(q-1)!$; multiplying these quantities yields the formula.
--
--   **Formalization Note** The theorem evaluates `totalR` by integrating the allowance once per face with `faceVolume`.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, values paragraph and equation (25), p.24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.24: actual total allowance R in equation (25). -/
theorem affine_totalR_closed (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    totalR T (affineData q T) = affineRClosed q T := by sorry
