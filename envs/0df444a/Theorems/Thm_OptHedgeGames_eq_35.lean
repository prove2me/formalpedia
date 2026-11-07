-- Prove2me | Theorems.Thm_OptHedgeGames_eq_35
-- name    : OptHedgeGames.eq_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:43.040369+00:00
-- url     : https://prove2.me/theorems/2da1cee3-4ac6-425d-989c-64954b7389dd
-- title:
--   (35) — the two-player feedback estimate
-- statement:
--   In the two-player run with $0<\eta\le1/100$, for every $t\ge1$,
--   $$
--   \|\ell_2^{t+1}-\ell_2^t\|_\infty\le\|x_1^{t+1}-x_1^t\|_1\le3\eta(v^t+v^{t-1}).
--   $$
--   The input of player 2 moves only when player 1 moves, and player 1 moves only when their current losses have variance. The paper notes that this is the only place where the number of players matters.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - reading: the display says 'the lemma gives' with no separate hypothesis on η → 0 < η ≤ 1/100; reason: this is the hypothesis of Lemma 5.1, which the display applies
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), (35), p.19

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

namespace OptHedgeGames

/-- **Display (35)** (the two-player feedback estimate; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), (35), p.19). In the two-player run with
`0 < η ≤ 1/100`, for every `t ≥ 1`,
`∥ℓᵗ⁺¹₂ − ℓᵗ₂∥_∞ ≤ ∥xᵗ⁺¹₁ − xᵗ₁∥₁ ≤ 3η(vᵗ + vᵗ⁻¹)`.

**Formalization Note** `n ≥ 1`. The hypothesis on `η` is that of Lemma 5.1, which the display
applies. `∥·∥_∞` is the supremum norm of `Fin n → ℝ`. -/
theorem eq_35 {n : ℕ} (hn : 1 ≤ n) (G : Game n) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 100)
    (t : ℕ) (ht : 1 ≤ t) :
    ‖G.l2 η (t + 1) - G.l2 η t‖ ≤ l1Norm (G.x1 η (t + 1) - G.x1 η t) ∧
      l1Norm (G.x1 η (t + 1) - G.x1 η t) ≤ 3 * η * (G.v η t + G.v η (t - 1)) := by sorry

end OptHedgeGames
