-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_3
-- name    : OptHedgeGames.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:02.751788+00:00
-- url     : https://prove2.me/theorems/cc12fe98-4f99-4e87-9e96-436061f851a9
-- title:
--   Lemma 5.3 — the variance bound from the temporal approximation framework
-- statement:
--   There are absolute constants $C$ and $K_0$ such that in the two-player run, for every integer $W\ge K_0n$, every $\eta$ with $0<\eta W\le10^{-3}$ and every horizon $T\ge1$,
--   $$
--   \sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^t-\ell_1^{t-1})\le\frac14+C\Big[\Big(\frac{n^2}{W^2}+\eta^4n^2W^2\Big)\Big(\sum_{t=1}^T\mathrm{Var}_{x_1^t}(\ell_1^{t-1})+1\Big)+\eta^2W\Big].
--   $$
--   The factor $n^2/W^2$ comes from the Bernstein inequality, the factor $\eta^4n^2W^2$ from the freezing error, and the term $\eta^2W$ from the two ends of the horizon.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - encoding: absolute constants C and K₀ → 0 < C, 0 < K₀, both before all data; reason: enlarging C or K₀ keeps the statement true, so positivity excludes nothing
--   - encoding: the horizon T, a number of rounds (§2, p.4; Theorem 3.4 says T ≥ 1) → 1 ≤ T; reason: T = 0 is no horizon; the source's horizon is a positive number of rounds
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.3, (37), p.21

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

namespace OptHedgeGames

/-- **Lemma 5.3** (variance bound resulting from the temporal approximation framework; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.3,
p.21). There are absolute constants `C` and `K₀` such that for every integer `W ≥ K₀n` and every `η` with
`0 < ηW ≤ 10⁻³`,
`Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ₁ − ℓᵗ⁻¹₁) ≤ 1/4 + C[(n²/W² + η⁴n²W²)(Σ_{t=1}^T Var_{xᵗ₁}(ℓᵗ⁻¹₁) + 1) + η²W]`, which is (37).

**Formalization Note** `C` and `K₀` come before `n`, `W`, `η`, the game and `T`. `0 < ηW` forces
`W ≥ 1`. `n ≥ 1`, `T ≥ 1`. -/
theorem lemma_5_3 : ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
    ∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (W : ℕ) (η : ℝ), K₀ * (n : ℝ) ≤ (W : ℝ) →
      0 < η * W → η * W ≤ 1 / 1000 → ∀ T : ℕ, 1 ≤ T →
        totalVariation (G.x1 η) (G.l1 η) T ≤
          1 / 4 + C * (((n : ℝ) ^ 2 / (W : ℝ) ^ 2 + η ^ 4 * (n : ℝ) ^ 2 * (W : ℝ) ^ 2) *
              (cumVariance (G.x1 η) (G.l1 η) T + 1) + η ^ 2 * W) := by sorry

end OptHedgeGames
