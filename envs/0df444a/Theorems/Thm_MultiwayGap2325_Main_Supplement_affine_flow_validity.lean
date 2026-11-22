-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_validity
-- name    : MultiwayGap2325.Main.Supplement.affine_flow_validity
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:17:34.585555+00:00
-- url     : https://prove2.me/theorems/69aae834-949b-4e00-8a95-c9ea5496ace2
-- title:
--   The affine construction is a flow instance
-- statement:
--   For every integer $q\ge2$ and real $T\in(1/2,1)$, the explicit data (23)–(24) form a flow instance on $\Delta_q$. Thus they simultaneously satisfy the regularity requirements of §5.1, the capacity inequality (8), the terminal boundary condition, and conservation (9).
--
--   This is the validity half of Theorem 6.1. The paper establishes normal continuity from the one-cell subdivision, proves capacity using $|I|(r-|I|)/(r-1)\ge1$, checks the terminal facets using $p_i^S=0$, and verifies conservation by the scale recurrence for $a_r$ together with the top-face allowance.
--
--   **Formalization Note** `IsFlowInstance` bundles exactly `Regular`, `Capacity`, `TerminalCondition`, and `Conservation`; all four are conclusions for `affineData q T`, not input assumptions.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 6.1 and its validity proof, pp.23–24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, pp.23–24: regularity, capacity, terminal condition and conservation for the explicit affine data. -/
theorem affine_flow_validity (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    IsFlowInstance T (affineData q T) := by sorry
