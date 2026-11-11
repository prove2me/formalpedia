-- Prove2me | Theorems.Thm_HarmonicRanking_Main_main_competitive_ratio
-- name    : HarmonicRanking.Main.main_competitive_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:03.057322+00:00
-- url     : https://prove2.me/theorems/a60d4c1a-b836-4d35-a630-4f69fe64a18b
-- title:
--   Theorem 1.1 — Harmonic Ranking competitive ratio
-- statement:
--   The explicit score $h^\star$ defined by the 240 integer heights of §6 is a positive nonincreasing right-continuous score on $[0,1)$. It is fixed independently of all instances. For every finite instance $G=(L,R,w,E)$ with arbitrary nonnegative real potential weights and any admissible rule,
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge\frac{698015475248}{10^{12}}\operatorname{OPT}(G)
--   =0.698015475248\operatorname{OPT}(G).
--   $$
--
--   The expectation samples independent uniform ranks in $[0,1)$ on both vertex sides. The algorithm is the actual harmonic-priority query–commit scan. Empty vertex sides, empty realized graphs, and zero weights are included. This identifies the source's explicit score witness constructively and asserts the full exact competitive ratio without certificate assumptions.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
--   - encoding: there exists an explicit score h-star with a uniform guarantee → the fixed score defined by the exact p. 19 prescription is a score and has that guarantee for every instance; reason: naming and checking the displayed witness recovers the source existential statement with the same constant and full instance class
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 2, Theorem 1.1

import Definitions.Def_HarmonicRanking_Main_Scan
import Definitions.Def_HarmonicRanking_Main_ExplicitScore

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem main_competitive_ratio :
    IsScore explicitScore ∧
    ∀ {L R : Type*} [Fintype L] [Fintype R] (G : Instance L R)
      (τ : TieRule L R), Admissible explicitScore G.weight τ →
      competitiveFactor * OPT G ≤ expectedALG G τ := by sorry

end HarmonicRanking.Main
