-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_1
-- name    : OptHedgeGames.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:34.36884+00:00
-- url     : https://prove2.me/theorems/5500ea90-ac97-4125-8796-8c6ae0083b59
-- title:
--   Lemma 5.1 — movement and variance shift
-- statement:
--   In the two-player run with loss matrices $A,B\in[0,1]^{n\times n}$, let $0<\eta\le1/100$. For every $t\ge1$ and action $a$,
--   $$
--   e^{-3\eta}\le\frac{x_1^{t+1}(a)}{x_1^t(a)}\le e^{3\eta},\qquad\|x_1^{t+1}-x_1^t\|_1\le3\eta(v^t+v^{t-1}),
--   $$
--   and for every horizon $T\ge1$,
--   $$
--   \sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^t)\le e^{3\eta}\sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^{t-1})+\frac14.
--   $$
--   So player 1 moves only as much as their own variance allows.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - encoding: the horizon T, a number of rounds (§2, p.4; Theorem 3.4 says T ≥ 1) → 1 ≤ T; reason: T = 0 is no horizon; the source's horizon is a positive number of rounds
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.1, (33), (34), p.18

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

namespace OptHedgeGames

/-- **Lemma 5.1** (movement and variance shift; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.1, p.18). In the two-player run, let
`0 < η ≤ 1/100`. For every `t ≥ 1`, `e^{−3η} ≤ xᵗ⁺¹₁(a)/xᵗ₁(a) ≤ e^{3η}` for all actions `a` and
`∥xᵗ⁺¹₁ − xᵗ₁∥₁ ≤ 3η(vᵗ + vᵗ⁻¹)`, which is (33); and
`Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ₁) ≤ e^{3η} Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ⁻¹₁) + 1/4`, which is (34).

**Formalization Note** `n ≥ 1` (§5 says `n ≥ 2`; at `n = 1` every variance vanishes and the claims
hold). The iterates have positive entries, so the quotient is genuine. `t - 1` is read at `t ≥ 1`. -/
theorem lemma_5_1 {n : ℕ} (hn : 1 ≤ n) (G : Game n) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 100) :
    (∀ t : ℕ, 1 ≤ t →
      (∀ a, Real.exp (-(3 * η)) ≤ G.x1 η (t + 1) a / G.x1 η t a ∧
        G.x1 η (t + 1) a / G.x1 η t a ≤ Real.exp (3 * η)) ∧
      l1Norm (G.x1 η (t + 1) - G.x1 η t) ≤ 3 * η * (G.v η t + G.v η (t - 1))) ∧
    (∀ T : ℕ, 1 ≤ T →
      ∑ t ∈ Finset.Icc 1 T, var (G.x1 η t) (G.l1 η t) ≤
        Real.exp (3 * η) * cumVariance (G.x1 η) (G.l1 η) T + 1 / 4) := by sorry

end OptHedgeGames
