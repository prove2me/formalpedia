-- Prove2me | Theorems.Thm_OptHedgeGames_eq_44_45
-- name    : OptHedgeGames.eq_44_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:31.051201+00:00
-- url     : https://prove2.me/theorems/8e6a52a9-ed54-4084-90fc-553644e0e49c
-- title:
--   (44)–(45) — the freezing error in position and in derivative
-- statement:
--   In the two-player run, for integers $W\ge1$, all $\eta$ with $0<\eta W\le10^{-3}$ and every anchor $t_0\ge2$,
--   $$
--   \|Y(s)-\bar Y(s)\|_1\le6\eta W\delta_{t_0},\qquad\|L(s)-\bar L(s)\|_\infty\le6\eta W\delta_{t_0}\qquad(s\in[t_0,t_0+3W]),
--   $$
--   and for $s\in(j,j+1)$ with $t_0\le j\le t_0+3W-1$,
--   $$
--   \|L'(s)-\bar L'(s)\|_\infty\le\|Y'(s)-\bar Y'(s)\|_1\le\eta(2\delta_{t_0}+18\eta W\delta_{t_0})\le3\eta\delta_{t_0}.
--   $$
--   The derivative error carries no factor $W$. The paper notes that this is essential, and it is why the derivative error is estimated directly.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - generalization: anchor t₀ with t₀ + 3W ≤ T (p.22) → anchor t₀ ≥ 2, no horizon T; reason: the run is infinite in Lean and the statement reads no round past t₀ + 3W; the source's anchors are instances
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), proof of Lemma 5.6, (44), (45), p.23

import Mathlib
import Definitions.Def_OptHedgeGames_Interpolation

namespace OptHedgeGames

/-- **Displays (44)–(45)** (freezing error in position and in derivative; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), proof of Lemma 5.6,
(44), (45), p.23). For integers `W ≥ 1`, all `η` with `0 < ηW ≤ 10⁻³` and `t₀ ≥ 2`:
`∥Y(s) − Ȳ(s)∥₁ ≤ 6ηWδ_{t₀}` and `∥L(s) − L̄(s)∥_∞ ≤ 6ηWδ_{t₀}` for `s ∈ J_{t₀}`, which is (44); and for
`s ∈ (j, j + 1)` with `t₀ ≤ j ≤ t₀ + 3W − 1`,
`∥L′(s) − L̄′(s)∥_∞ ≤ ∥Y′(s) − Ȳ′(s)∥₁ ≤ η(2δ_{t₀} + 18ηWδ_{t₀}) ≤ 3ηδ_{t₀}`, which is (45).

**Formalization Note** (45) is stated on the open unit intervals, as the source does ("for
`s ∈ (j, j+1)`"), since `deriv` at an integer may be the junk `0` at a corner of `L`. The paper's
`t₀ + 3W ≤ T` is dropped: the run is infinite in Lean and no round past `t₀ + 3W` is read. `n ≥ 1`. -/
theorem eq_44_45 {n : ℕ} (hn : 1 ≤ n) (G : Game n) (W : ℕ) (η : ℝ) (hW : 1 ≤ W)
    (hη : 0 < η * W) (hη' : η * W ≤ 1 / 1000) (t₀ : ℕ) (ht₀ : 2 ≤ t₀) :
    (∀ s : ℝ, (t₀ : ℝ) ≤ s → s ≤ (t₀ : ℝ) + 3 * W →
      l1Norm (G.Y η s - G.Ybar η t₀ s) ≤ 6 * η * W * G.delta η W t₀ ∧
        ‖G.L η s - G.Lbar η t₀ s‖ ≤ 6 * η * W * G.delta η W t₀) ∧
    (∀ j : ℕ, t₀ ≤ j → j ≤ t₀ + 3 * W - 1 → ∀ s : ℝ, (j : ℝ) < s → s < (j : ℝ) + 1 →
      ‖deriv (G.L η) s - deriv (G.Lbar η t₀) s‖ ≤ l1Norm (deriv (G.Y η) s - deriv (G.Ybar η t₀) s) ∧
        l1Norm (deriv (G.Y η) s - deriv (G.Ybar η t₀) s) ≤
          η * (2 * G.delta η W t₀ + 18 * η * W * G.delta η W t₀) ∧
        η * (2 * G.delta η W t₀ + 18 * η * W * G.delta η W t₀) ≤ 3 * η * G.delta η W t₀) := by sorry

end OptHedgeGames
