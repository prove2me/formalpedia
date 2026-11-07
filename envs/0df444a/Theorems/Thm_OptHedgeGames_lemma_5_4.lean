-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_4
-- name    : OptHedgeGames.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:05.18683+00:00
-- url     : https://prove2.me/theorems/7a9fd188-93c3-43c6-8155-956fdcbca4e7
-- title:
--   Lemma 5.4 — the two-player variation–variance inequality
-- statement:
--   There is an absolute constant $c>0$ such that if both players run Optimistic Hedge with $0<\eta\le c/n$, then for every horizon $T\ge1$,
--   $$
--   \sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^t-\ell_1^{t-1})\le\frac1{64}\sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^{t-1})+\frac12.
--   $$
--   Combined with Lemma 3.1, this yields the constant regret bound of Theorem 3.4.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - encoding: the horizon T, a number of rounds (§2, p.4; Theorem 3.4 says T ≥ 1) → 1 ≤ T; reason: T = 0 is no horizon; the source's horizon is a positive number of rounds
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.4, (38), p.21

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

namespace OptHedgeGames

/-- **Lemma 5.4** (two-player variation–variance inequality; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.4, p.21). There is an absolute
constant `c > 0` such that if both players run Optimistic Hedge with `0 < η ≤ c/n`, then
`Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ₁ − ℓᵗ⁻¹₁) ≤ (1/64) Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ⁻¹₁) + 1/2`, which is (38).

**Formalization Note** `c` comes before `n`, the game, `η` and `T`. `n ≥ 1`, `T ≥ 1`. -/
theorem lemma_5_4 : ∃ c : ℝ, 0 < c ∧
    ∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (η : ℝ), 0 < η → η ≤ c / (n : ℝ) → ∀ T : ℕ, 1 ≤ T →
      totalVariation (G.x1 η) (G.l1 η) T ≤
        1 / 64 * cumVariance (G.x1 η) (G.l1 η) T + 1 / 2 := by sorry

end OptHedgeGames
