-- Prove2me | Theorems.Thm_HarmonicRanking_Main_section_cutoffs
-- name    : HarmonicRanking.Main.section_cutoffs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:28.585591+00:00
-- url     : https://prove2.me/theorems/8dd14261-8210-4da3-920b-1d9224c11a32
-- title:
--   Corollary 3.2 — the two section cutoffs
-- statement:
--   Fix $h,G,\tau$, a realized target edge $uv$, and all other ranks. Let $a(x),b(y)$ be the infimum-defined section cutoffs. Each belongs to $[0,1]$, and for every $x,y\in[0,1)$,
--
--   $$
--   y>a(x)\Rightarrow u\text{ strictly earlier than }v,\qquad
--   y<a(x)\Rightarrow v\text{ no later than }u,
--   $$
--   $$
--   x>b(y)\Rightarrow v\text{ strictly earlier than }u,\qquad
--   x<b(y)\Rightarrow u\text{ no later than }v.
--   $$
--
--   Each assertion uses the run with the two displayed target ranks. Neither assertion classifies its boundary. The functions need not be monotone across sections. This supplies the source's two section cutoffs for later gain comparisons.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
--   - reading: the symmetric sentence says that x>b(y) exactly describes the region where v is strictly earlier, following an initial boundary qualification → both directions of the symmetric description are asserted away from x=b(y), as for a(x); reason: Symmetrically and the proof by interchanging u and v carry the boundary qualification to b; Example 3.3 confirms boundary membership is tie-dependent
--   - encoding: the cutoffs are the infima in the proof, with empty and full section conventions → each cutoff is sInf of its section with the endpoint 1 inserted; reason: the set is nonempty and bounded in [0,1]; empty and full sections have values 1 and 0
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 11, Corollary 3.2

import Definitions.Def_HarmonicRanking_Main_Cutoffs

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem section_cutoffs
    {L R : Type*} [Fintype L] [Fintype R]
    (h : ℝ → ℝ) (hh : IsScore h) (G : Instance L R)
    (τ : TieRule L R) (hτ : Admissible h G.weight τ)
    (u : L) (v : R) (huv : (u,v) ∈ G.realized) (ρ : Ranks L R) :
    (∀ x : Rank, cutoffA G τ ρ u v x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ y : Rank,
        (cutoffA G τ ρ u v x < y →
          earlier G τ (targetRanks ρ u v x y) (Sum.inl u) (Sum.inr v)) ∧
        ((y : ℝ) < cutoffA G τ ρ u v x →
          matchTime G.realized (τ (targetRanks ρ u v x y)) (Sum.inr v) ≤
          matchTime G.realized (τ (targetRanks ρ u v x y)) (Sum.inl u))) ∧
    (∀ y : Rank, cutoffB G τ ρ u v y ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ x : Rank,
        (cutoffB G τ ρ u v y < x →
          earlier G τ (targetRanks ρ u v x y) (Sum.inr v) (Sum.inl u)) ∧
        ((x : ℝ) < cutoffB G τ ρ u v y →
          matchTime G.realized (τ (targetRanks ρ u v x y)) (Sum.inl u) ≤
          matchTime G.realized (τ (targetRanks ρ u v x y)) (Sum.inr v))) := by sorry

end HarmonicRanking.Main
