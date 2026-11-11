-- Prove2me | Theorems.Thm_HarmonicRanking_Main_finite_algorithmic_bound
-- name    : HarmonicRanking.Main.finite_algorithmic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:08.586348+00:00
-- url     : https://prove2.me/theorems/c7fda6ea-4ae0-4bfd-8167-2dfda5464f43
-- title:
--   Theorem 5.3 — finite cut–flow algorithmic guarantee
-- statement:
--   Fix $m\ge1$ and positive nonincreasing real heights $H$. Let $G$ be any finite edge-weighted oblivious instance and use any admissible rule for the step score $h^{(m)}$. Then
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]\ge\operatorname{MC}_m(H)\operatorname{OPT}(G)
--   =\operatorname{MF}_m(H)\operatorname{OPT}(G).
--   $$
--
--   The displayed equality and competitive inequality are both retained. The weights, graph realization, continuous ranks, and admissible ties have their full source domains. This gives the algorithmic interpretation of every finite-profile cut or flow value.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - generalization: measurable total scan order in the ranks → each finite scan position is a.e. measurable for the product rank law, with local monotonicity at every rank assignment; reason: every source measurable order qualifies; the additional completion-measurable orders have measurable versions and bounded rewards, so all original rules remain covered
--   - encoding: cell indices 1 through m, threshold counts 0 through m → Fin m cell indices are shifted down by one and Fin (m+1) threshold counts are unchanged; reason: the same cells, adjacent arcs, and last-cell increments are represented bijectively
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 19, Theorem 5.3

import Definitions.Def_HarmonicRanking_Main_Scan
import Definitions.Def_HarmonicRanking_Main_Network

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem finite_algorithmic_bound
    {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H)
    {L R : Type*} [Fintype L] [Fintype R] (G : Instance L R)
    (τ : TieRule L R) (hτ : Admissible (stepScore H) G.weight τ) :
    MC H * OPT G ≤ expectedALG G τ ∧ MC H * OPT G = MF H * OPT G := by sorry

end HarmonicRanking.Main
