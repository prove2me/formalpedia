-- Prove2me | Theorems.Thm_HarmonicRanking_Main_exact_certificate
-- name    : HarmonicRanking.Main.exact_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:42.376089+00:00
-- url     : https://prove2.me/theorems/a0887268-5c82-4fe5-8102-cfe713b8ae5f
-- title:
--   Theorem 6.2 — exactly verified 240-step score function
-- statement:
--   Let $H$ be the fixed integer height vector prescribed by the exact real-floor formula on p. 19, and let $h^\star$ be its step score. Unconditionally,
--
--   $$
--   \operatorname{MF}_{240}(H)=\operatorname{MC}_{240}(H)
--   \ge\frac{698015475248}{10^{12}}=0.698015475248>0.698.
--   $$
--
--   This is a lower bound for the exact network. It does not assert that its optimum equals the displayed constant. Neither a feasible certificate nor the checker's success is a hypothesis. Proving the theorem requires a justified certificate for these fixed definitions; the external artifact has not been independently run in this drafting pass.
--
--   Differences from the source:
--   - encoding: the supplied integer score list, specified by the exact generating formula on p. 19 → the height vector is defined directly by that exact real-floor prescription; reason: the manuscript says the formula generates the checked list; no unverified equality or certificate conclusion is assumed
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 20, Theorem 6.2

import Definitions.Def_HarmonicRanking_Main_ExplicitScore

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem exact_certificate :
    MF explicitHeights = MC explicitHeights ∧
    competitiveFactor ≤ MC explicitHeights ∧
    competitiveFactor = (0.698015475248 : ℝ) ∧
    (0.698 : ℝ) < competitiveFactor := by sorry

end HarmonicRanking.Main
