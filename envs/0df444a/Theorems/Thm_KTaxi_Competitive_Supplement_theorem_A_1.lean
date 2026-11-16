-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_theorem_A_1
-- name    : KTaxi.Competitive.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:18.034341+00:00
-- url     : https://prove2.me/theorems/19fb0476-7a8b-404d-96fb-22746c9bff25
-- title:
--   Theorem A.1 — universal randomized two-taxi lower bound 9 on ℤ
-- statement:
--   Let $A$ be any randomized online hard two-taxi strategy on the integer line, with arbitrary private randomness, memory, and extra paid movements. From the common initial configuration $\{-1,1\}$, every finite $0\le\rho<9$ and $\beta\ge0$ admit a visible adaptive online adversary and a finite horizon $T$ such that
--   $$\mathbb E[A_T]>\rho\mathbb E[\mathrm{ADV}_T]+\beta,\qquad \mathbb E[\mathrm{ADV}_T]<\infty.$$
--   Each adversary request and comparator serving decision uses only previously completed public actions and is fixed before the current response. Laziness is a reduction in the source proof and is not a hypothesis here. This is an independent companion theorem establishing the universal lower bound already on $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: arbitrary randomized online hard-taxi algorithms → causal policies on arbitrary private probability spaces with paid moves before pickup and after drop-off and a detour surcharge; reason: the full private tape encodes arbitrary memory; endpoints and surcharge represent every terminating round with identical hard cost, and the lower-bound adversary uses only these visible endpoints and serving actions
--   - encoding: expected nonnegative hard costs → extended nonnegative real expectations; reason: retains infinite costs and charges only paid movement, with no nonintegrable Bochner default
--   - encoding: competitive ratio at least 9 → every 0 ≤ ρ < 9 and finite β has a bounded-horizon strict counterexample from {−1,1} with finite expected comparator cost; reason: Appendix A fixes this start and proves the contradiction using bounded truncations; the negative formulation preserves additive constants and the exact lower bound
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem A.1, PDF p. 17 (printed p. 16)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Adaptive

open scoped ENNReal NNReal

universe u

namespace KTaxi.Competitive.Supplement

/-- Theorem A.1, PDF p. 17: every randomized strategy, with arbitrary private
probability space, history and paid movements, on the INTEGER line. The comparator
chooses its serving taxi before the current response. All witnesses have bounded horizon. -/
theorem theorem_A_1 (A : IntegerStrategy.{u} 2) (ρ β : ℝ≥0) (hρ : ρ < 9) :
    ∃ (D : VisibleAdversary ℤ 2) (T : ℕ),
      let x₀ : Fin 2 → ℤ := fun i => if i = 0 then -1 else 1
      integerAdvCost A D T x₀ < ⊤ ∧
      (ρ : ℝ≥0∞) * integerAdvCost A D T x₀ + (β : ℝ≥0∞) <
        integerAlgCost A D T x₀ := by sorry

end KTaxi.Competitive.Supplement
