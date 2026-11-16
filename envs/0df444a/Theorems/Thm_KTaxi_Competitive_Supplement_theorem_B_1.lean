-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_theorem_B_1
-- name    : KTaxi.Competitive.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:54.100199+00:00
-- url     : https://prove2.me/theorems/1492be51-d558-4348-a26f-e0607f54b209
-- title:
--   Theorem B.1 — Algorithm 1 has matching lower bound 9^(k−1)
-- statement:
--   For every integer $k\ge2$, use exactly the published Algorithm 1 on the full real line, starting with all taxis at zero. For every finite $0\le\rho<9^{k-1}$ and $\beta\ge0$, there exists a visible adaptive online adversary and a finite horizon $T$ satisfying
--   $$\mathbb E[\mathrm{ALG}_T]>\rho\mathbb E[\mathrm{ADV}_T]+\beta,\qquad \mathbb E[\mathrm{ADV}_T]<\infty.$$
--   Both players start at zero. The comparator uses ordinary serving moves and chooses each request and serving taxi before the current randomized response. It sees only visible completed actions, not Algorithm 1’s hidden ranking. This companion theorem establishes tightness of the mission’s exact upper bound for this algorithm; it does not assert a universal lower bound for all algorithms.
--
--   Differences from the source:
--   - encoding: expected nonnegative hard costs → extended nonnegative real expectations; reason: retains infinite costs and charges only paid movement, with no nonintegrable Bochner default
--   - encoding: adaptive online adversary based on past actions → a visible-history adversary embedded into the published game by a replay adapter that discards every internal state; reason: the base model exposes hidden states, so the adapter restricts witnesses to the paper’s legal observations and ordinary serving moves
--   - encoding: competitive ratio at least 9^(k−1) → every smaller nonnegative ratio and finite β has a bounded-horizon strict counterexample from the common all-zero start with finite expected comparator cost; reason: Appendix B supplies finite N,L approximations followed by spatial scaling, so no finite witness is claimed to attain the limiting ratio
--   - encoding: k ≥ 2 → k ≥ 2 together with the redundant instance NeZero k required by the published algorithm interface; reason: the instance is automatically available for every k ≥ 2 and excludes no source case
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem B.1, PDF p. 19 (printed p. 18)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Adaptive

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-- Theorem B.1, PDF p. 19: exact lower bound for the published Algorithm 1,
from the common all-zero start. Witnesses use visible completed actions, never ranks. -/
theorem theorem_B_1 (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (ρ β : ℝ≥0) (hρ : ρ < 9 ^ (k - 1)) :
    ∃ (D : VisibleAdversary ℝ k) (T : ℕ),
      let x₀ : Fin k → ℝ := fun _ => 0
      let adv : Adversary ℝ k (algorithm1 ℝ k).State := toBaseAdversary D x₀ x₀
      advCost (algorithm1 ℝ k) adv T x₀ x₀ < ⊤ ∧
      (ρ : ℝ≥0∞) * advCost (algorithm1 ℝ k) adv T x₀ x₀ + (β : ℝ≥0∞) <
        algCost (algorithm1 ℝ k) adv T x₀ x₀ := by sorry

end KTaxi.Competitive.Supplement
