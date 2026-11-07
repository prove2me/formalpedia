-- Prove2me | Theorems.Thm_OptHedgeGames_eq_43
-- name    : OptHedgeGames.eq_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:32.315216+00:00
-- url     : https://prove2.me/theorems/9301d716-14e0-4c2c-9662-30c0851ae9c3
-- title:
--   (43) — the Bernstein bound for the frozen curve
-- statement:
--   There is an absolute constant $C$ such that the following holds in the two-player run for all integers $W\ge1$, all $\eta$ with $0<\eta W\le10^{-3}$, every anchor $t_0\ge2$ and every fixed probability vector $p$. With $J_{t_0}=[t_0,t_0+3W]$, $I_{t_0}=[t_0+W,t_0+2W]$ and $\|F\|_{L^2(I;p)}=(\int_I\|F(s)\|_p^2ds)^{1/2}$,
--   $$
--   \|\bar L'\|_{L^2(I_{t_0};p)}\le\Big(\frac{2ne^{3\eta W}}{W}+\eta\Big)\|\bar L\|_{L^2(J_{t_0};p)}\le C\frac nW\|\bar L\|_{L^2(J_{t_0};p)}.
--   $$
--   When player 2's losses are frozen, player 1's losses are a ratio of two exponential sums, so Lemma 5.2 applies to them.
--
--   Differences from the source:
--   - generalization: n ≥ 2 actions (Setting and notation of §5, p.18) → n ≥ 1; reason: at n = 1 every variance vanishes and the claim still holds; n ≥ 2 is an instance
--   - generalization: anchor t₀ with t₀ + 3W ≤ T (p.22) → anchor t₀ ≥ 2, no horizon T; reason: the run is infinite in Lean and the statement reads no round past t₀ + 3W; the source's anchors are instances
--   - reading: a chain whose first step reads N = L̄Z, with N and Z internal to the proof → the second and third terms of the chain, with ‖L̄′‖ on the left; reason: N is not an object of the statement; the conclusion and its explicit middle constant are kept
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), proof of Lemma 5.6, (43), p.23

import Mathlib
import Definitions.Def_OptHedgeGames_Interpolation

namespace OptHedgeGames

/-- **Display (43)** (Bernstein bound for the frozen curve; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), proof of Lemma 5.6, (43), p.23).
There is an absolute constant `C` such that for all integers `W ≥ 1`, all `η` with `0 < ηW ≤ 10⁻³`, every
anchor `t₀ ≥ 2` and every fixed probability vector `p`,
`∥L̄′∥_{L²(I_{t₀};p)} ≤ (2ne^{3ηW}/W + η) ∥L̄∥_{L²(J_{t₀};p)} ≤ C (n/W) ∥L̄∥_{L²(J_{t₀};p)}`, where `J_{t₀} = [t₀, t₀ + 3W]`, `I_{t₀} = [t₀ + W, t₀ + 2W]`
and `∥F∥_{L²(I;p)} = (∫_I ∥F(s)∥²_p ds)^{1/2}`.

**Formalization Note** The display's first step goes through `N`, internal to the proof, and is left
out; the two steps stated here read only `L̄`. `C` comes before `n`, `W`, `η`, the game, `t₀` and `p`. The paper's
`t₀ + 3W ≤ T` is dropped, because the run in Lean is infinite and the bound reads no round past
`t₀ + 3W`. `n ≥ 1`. -/
theorem eq_43 : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (W : ℕ) (η : ℝ), 1 ≤ W → 0 < η * W → η * W ≤ 1 / 1000 →
      ∀ t₀ : ℕ, 2 ≤ t₀ → ∀ p : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) →
        Real.sqrt (∫ s in ((t₀ : ℝ) + W)..((t₀ : ℝ) + 2 * W), var p (deriv (G.Lbar η t₀) s)) ≤
            (2 * (n : ℝ) * Real.exp (3 * η * W) / W + η) *
              Real.sqrt (∫ s in (t₀ : ℝ)..((t₀ : ℝ) + 3 * W), var p (G.Lbar η t₀ s)) ∧
          (2 * (n : ℝ) * Real.exp (3 * η * W) / W + η) *
              Real.sqrt (∫ s in (t₀ : ℝ)..((t₀ : ℝ) + 3 * W), var p (G.Lbar η t₀ s)) ≤
            C * ((n : ℝ) / W) *
              Real.sqrt (∫ s in (t₀ : ℝ)..((t₀ : ℝ) + 3 * W), var p (G.Lbar η t₀ s)) := by sorry

end OptHedgeGames
