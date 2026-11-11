-- Prove2me | Theorems.Thm_HarmonicRanking_Main_rounded_flow_transfer
-- name    : HarmonicRanking.Main.rounded_flow_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:58.077805+00:00
-- url     : https://prove2.me/theorems/9d694a76-98a7-4702-9058-ee8968b9f34c
-- title:
--   Lemma 6.1 — rounded integer flow transfers exactly
-- statement:
--   Use the fixed 240-step heights $H$ from §6 and their individually rounded integer network at scale $10^{12}$. Let $f$ be any feasible integer flow, and let $F\in\mathbb Z$ be its net source value. Then
--
--   $$
--   \operatorname{MC}_{240}(H)=\operatorname{MF}_{240}(H)\ge\frac F{10^{12}}.
--   $$
--
--   Feasibility refers to the rounded capacities and conservation equations, rather than an assumed exact-network bound. The statement transfers an arbitrary actual rounded flow value to the exact network.
--
--   Differences from the source: none.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 20, Lemma 6.1

import Definitions.Def_HarmonicRanking_Main_ExplicitScore

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem rounded_flow_transfer (f : StepArc 240 → ℤ) (hf : IntegerFeasible f) (F : ℤ)
    (hF : integerFlowValue f = F) :
    MC explicitHeights = MF explicitHeights ∧
      (F : ℝ) / 10^12 ≤ MF explicitHeights := by sorry

end HarmonicRanking.Main
