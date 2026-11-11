-- Prove2me | Theorems.Thm_HarmonicRanking_Main_cutoff_monotonicity
-- name    : HarmonicRanking.Main.cutoff_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:09.32077+00:00
-- url     : https://prove2.me/theorems/9ae354d1-e9d6-4ffe-9194-e339be094cd2
-- title:
--   Lemma 3.1 — one-rank matching-order monotonicity
-- statement:
--   Fix a score $h$, an instance $G$, an admissible rule $\tau$, and a realized target edge $uv$. Hold all ranks except that of $v$ fixed. For any $t,t'\in[0,1)$ with $t<t'$, let $\rho^t$ be the assignment with $v$'s rank replaced by $t$. Then
--
--   $$
--   u\text{ strictly earlier than }v\text{ at }\rho^t
--   \quad\Longrightarrow\quad
--   u\text{ strictly earlier than }v\text{ at }\rho^{t'}.
--   $$
--
--   Unmatched vertices are later than every matched vertex. This is the section-order property used to define the two cutoffs; it does not assert monotonicity of entire cutoff curves.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 10, Lemma 3.1

import Definitions.Def_HarmonicRanking_Main_Cutoffs

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem cutoff_monotonicity
    {L R : Type*} [Fintype L] [Fintype R]
    (h : ℝ → ℝ) (hh : IsScore h) (G : Instance L R)
    (τ : TieRule L R) (hτ : Admissible h G.weight τ)
    (u : L) (v : R) (huv : (u,v) ∈ G.realized)
    (ρ : Ranks L R) (t t' : Rank) (htt : t < t') :
    earlier G τ (targetRanks ρ u v (ρ (Sum.inl u)) t) (Sum.inl u) (Sum.inr v) →
    earlier G τ (targetRanks ρ u v (ρ (Sum.inl u)) t') (Sum.inl u) (Sum.inr v) := by sorry

end HarmonicRanking.Main
