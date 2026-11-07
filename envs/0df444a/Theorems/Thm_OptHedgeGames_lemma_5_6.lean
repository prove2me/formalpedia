-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_6
-- name    : OptHedgeGames.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:35.972296+00:00
-- url     : https://prove2.me/theorems/37df8788-db25-47a1-8382-905781963019
-- title:
--   Lemma 5.6 — the local energy estimate
-- statement:
--   There is an absolute constant $C$ such that in the two-player run, for all integers $W\ge1$, all $\eta$ with $0<\eta W\le10^{-3}$ and every anchor $t_0\ge2$,
--   $$
--   \int_{t_0+W}^{t_0+2W}\mathrm{Var}_{x_1^{\lfloor s\rfloor}}(L'(s))\,ds\le C\frac{n^2}{W^2}\int_{t_0}^{t_0+3W}\mathrm{Var}_{x_1^{\lfloor s\rfloor}}(L(s))\,ds+C\eta^2n^2W^2u_{t_0}.
--   $$
--   The first term is what the frozen curve satisfies by Lemma 5.2, and the second is the price of freezing.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - generalization: anchor t₀ with t₀ + 3W ≤ T (p.22) → anchor t₀ ≥ 2, no horizon T; reason: the run is infinite in Lean and the statement reads no round past t₀ + 3W; the source's anchors are instances
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.6, (42), p.22

import Mathlib
import Definitions.Def_OptHedgeGames_Interpolation

namespace OptHedgeGames

/-- **Lemma 5.6** (local energy estimate; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.6, p.22). There is an absolute constant `C` such
that for all integers `W ≥ 1` and all `η` with `0 < ηW ≤ 10⁻³`, every anchor `t₀ ≥ 2` satisfies
`∫_{I_{t₀}} Var_{x₁^{⌊s⌋}}(L′(s)) ds ≤ C (n²/W²) ∫_{J_{t₀}} Var_{x₁^{⌊s⌋}}(L(s)) ds + Cη²n²W² u_{t₀}`, which is (42).

**Formalization Note** `C` comes before `n`, `W`, `η`, the game and `t₀`. The paper's `t₀ + 3W ≤ T` is
dropped: the run is infinite in Lean and no round past `t₀ + 3W` is read. `t₀ ≥ 2` is kept, so that the
sum `u` starts at a round `r ≥ 1`. `n ≥ 1`. -/
theorem lemma_5_6 : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (W : ℕ) (η : ℝ), 1 ≤ W → 0 < η * W → η * W ≤ 1 / 1000 →
      ∀ t₀ : ℕ, 2 ≤ t₀ →
        (∫ s in ((t₀ : ℝ) + W)..((t₀ : ℝ) + 2 * W), var (G.x1 η ⌊s⌋₊) (deriv (G.L η) s)) ≤
          C * ((n : ℝ) ^ 2 / (W : ℝ) ^ 2) *
              (∫ s in (t₀ : ℝ)..((t₀ : ℝ) + 3 * W), var (G.x1 η ⌊s⌋₊) (G.L η s)) +
            C * η ^ 2 * (n : ℝ) ^ 2 * (W : ℝ) ^ 2 * G.u η W t₀ := by sorry

end OptHedgeGames
