-- Prove2me | Theorems.Thm_HarmonicRanking_Main_cutoff_gain
-- name    : HarmonicRanking.Main.cutoff_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:13.826607+00:00
-- url     : https://prove2.me/theorems/209abddd-0fd4-4d3e-8398-5c0777e882f1
-- title:
--   Lemma 3.6 — endpoint gains at the two cutoffs
-- statement:
--   Fix a score $h$, an instance $G$, an admissible rule, a realized target edge $uv$, and a rank realization with target ranks $x=x_u$ and $y=x_v$. Write $a(x),b(y)$ for the constructed section cutoffs and $\alpha_u,\alpha_v$ for the actual endpoint credits. Both cases are asserted:
--
--   $$
--   uv\text{ not selected}\quad\Longrightarrow\quad
--   \alpha_u\ge g_h(x,a(x))w_{uv}\quad\text{and}\quad
--   \alpha_v\ge g_h(y,b(y))w_{uv},
--   $$
--   $$
--   uv\text{ selected}\quad\Longrightarrow\quad\alpha_u+\alpha_v=w_{uv}.
--   $$
--
--   Zero weights are allowed. The boundary convention $g_h(t,1)=0$ handles a cutoff equal to 1. This is the pointwise gain bound for the continuous objective, including the symmetric endpoint assertion.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
--   - encoding: cutoffs at the unsampled endpoint use equation (8) → gain explicitly overrides both boundary coordinates, including gain(1,1)=1/2; reason: the same boundary values are used and all sampled ranks remain strictly below 1
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 13, Lemma 3.6, Eq. (9)

import Definitions.Def_HarmonicRanking_Main_Cutoffs

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem cutoff_gain
    {L R : Type*} [Fintype L] [Fintype R]
    (h : ℝ → ℝ) (hh : IsScore h) (G : Instance L R)
    (τ : TieRule L R) (hτ : Admissible h G.weight τ)
    (u : L) (v : R) (huv : (u,v) ∈ G.realized) (ρ : Ranks L R) :
    ((u,v) ∉ selected G τ ρ →
      gain h (ρ (Sum.inl u)) (cutoffA G τ ρ u v (ρ (Sum.inl u))) * (G.weight (u,v) : ℝ) ≤
        credit h G τ ρ (Sum.inl u) ∧
      gain h (ρ (Sum.inr v)) (cutoffB G τ ρ u v (ρ (Sum.inr v))) * (G.weight (u,v) : ℝ) ≤
        credit h G τ ρ (Sum.inr v)) ∧
    ((u,v) ∈ selected G τ ρ →
      credit h G τ ρ (Sum.inl u) + credit h G τ ρ (Sum.inr v) = (G.weight (u,v) : ℝ)) := by sorry

end HarmonicRanking.Main
