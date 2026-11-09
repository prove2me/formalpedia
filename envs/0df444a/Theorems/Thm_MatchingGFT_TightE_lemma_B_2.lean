-- Prove2me | Theorems.Thm_MatchingGFT_TightE_lemma_B_2
-- name    : MatchingGFT.TightE.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:21.08207+00:00
-- url     : https://prove2.me/theorems/2f7f7174-3695-4d31-81ba-bf5e2b425e67
-- title:
--   Lemma B.2 — Measurable approximate threshold
-- statement:
--   For measurable $t(z)\in[0,1]$, $a(z)\ge0$, nonincreasing $Q_B$, and $\eta>0$, there is a measurable $x_\eta(z)\in[0,1)$ with $x_\eta(z)=0$ when $t(z)=0$ and, when $t(z)>0$, $x_\eta(z)<t(z)$ and $F(z,x_\eta(z))\ge\sup_{0\le x<t(z)}F(z,x)-\eta$; symmetrically for the seller objective with nondecreasing $Q_S$.
--
--   Differences from the source:
--   - reading: Q_B nonincreasing (the lemma names no integrability) → Q_B also integrable on (0,1); reason: Q_B is a quantile function of a finite-mean type throughout the paper (PDF pp. 8–9, 13), and for Q_B(x) = 1/x² the supremum is +∞, so no x_η exists
--   - encoding: Q_B : (0,1) → [0,∞), Q_S likewise → functions ℝ → ℝ with hypotheses on (0,1); reason: only values on (0,1) enter
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Lemma B.2, PDF p. 25

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Regions

open Set

namespace MatchingGFT.TightE

/-- Lemma B.2 (PDF p. 25): for measurable `t(z) ∈ [0, 1]`, `a(z) ≥ 0` and nonincreasing `Q_B`, and every
`η > 0`, there is a measurable `x_η(z) ∈ [0, 1)` with `x_η(z) = 0` when `t(z) = 0` and, when `t(z) > 0`,
`x_η(z) < t(z)` and `F(z, x_η(z)) ≥ sup_{0 ≤ x < t(z)} F(z, x) - η`; symmetrically for the seller objective. -/
theorem lemma_B_2 {Z : Type*} [MeasurableSpace Z] (η : ℝ) (hη : 0 < η) :
    (∀ (t a : Z → ℝ) (QB : ℝ → ℝ), Measurable t → Measurable a → (∀ z, t z ∈ Icc (0 : ℝ) 1) →
      (∀ z, 0 ≤ a z) → (∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ QB u) → AntitoneOn QB (Ioo 0 1) →
      MeasureTheory.IntegrableOn QB (Ioo 0 1) →
      ∃ x : Z → ℝ, Measurable x ∧ ∀ z, x z ∈ Ico (0 : ℝ) 1 ∧ (t z = 0 → x z = 0) ∧
        (0 < t z → x z < t z ∧
          buyerSectionProfit QB (a z) (t z) - η ≤ buyerThresholdProfit QB (a z) (x z))) ∧
    (∀ (t b : Z → ℝ) (QS : ℝ → ℝ), Measurable t → Measurable b → (∀ z, t z ∈ Icc (0 : ℝ) 1) →
      (∀ z, 0 ≤ b z) → (∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ QS u) → MonotoneOn QS (Ioo 0 1) →
      ∃ y : Z → ℝ, Measurable y ∧ ∀ z, y z ∈ Ico (0 : ℝ) 1 ∧ (t z = 0 → y z = 0) ∧
        (0 < t z → y z < t z ∧
          sellerSectionProfit QS (b z) (t z) - η ≤ sellerThresholdProfit QS (b z) (y z))) := by sorry

end MatchingGFT.TightE
