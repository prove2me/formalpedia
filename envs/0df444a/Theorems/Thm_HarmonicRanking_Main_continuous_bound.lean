-- Prove2me | Theorems.Thm_HarmonicRanking_Main_continuous_bound
-- name    : HarmonicRanking.Main.continuous_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:22.236417+00:00
-- url     : https://prove2.me/theorems/577ef3ae-d2f0-43b3-ae3e-810735269768
-- title:
--   Proposition 4.2 — continuous variational competitive bound
-- statement:
--   Let $h$ be any positive nonincreasing right-continuous score, $G$ any fixed finite edge-weighted oblivious instance, and $\tau$ an admissible rule. The continuous value $\gamma_{\rm EW}(h)$ is the infimum over all admissible measurable cutoff pairs of Definition 4.1. Then
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge\gamma_{\rm EW}(h)\operatorname{OPT}(G).
--   $$
--
--   The expectation is over independent continuous ranks on both vertex sides. The cutoff domain includes unrealizable pairs, with disjointness only almost everywhere and no cross-section monotonicity. This is the fixed-score variational competitive guarantee.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
--   - encoding: Lebesgue-measurable cutoff curves and their unit-square integrals → a.e. measurable curves for Lebesgue law and a product-measure integral on the closed unit square; reason: completion-measurable curves have measurable versions with identical payoffs; endpoint sets have measure zero and the analytical gain values are explicit
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 14, Proposition 4.2

import Definitions.Def_HarmonicRanking_Main_Scan
import Definitions.Def_HarmonicRanking_Main_Game

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem continuous_bound
    {L R : Type*} [Fintype L] [Fintype R]
    (h : ℝ → ℝ) (hh : IsScore h) (G : Instance L R)
    (τ : TieRule L R) (hτ : Admissible h G.weight τ) :
    gammaEW h * OPT G ≤ expectedALG G τ := by sorry

end HarmonicRanking.Main
