-- Prove2me | Theorems.Thm_LeiBR_Sync_fixed_point
-- name    : LeiBR.Sync.fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:33.004605+00:00
-- url     : https://prove2.me/theorems/7d39f892-42a6-459d-b789-0d50d1b44bd8
-- title:
--   Proof of Proposition 2 — a Nash equilibrium is a fixed point of the proximal BR map, $x^*_i=\hat x_i(x^*)$
-- statement:
--   Under Assumption 1, with $\mu>0$, let $\hat x$ be the proximal best-response map and let $x^*$ be a Nash equilibrium of the game. Then for every player $i$,
--   $$\hat x_i(x^*)=x^*_i .$$
--
--   This identity lets every iterate of a best-response scheme be compared with the equilibrium through the contraction (5)/(9).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, §3.2, proof of Proposition 2, p. 7

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame

open MeasureTheory

namespace LeiBR.Sync

/-- Proof of Proposition 2, §3.2, p. 7: a Nash equilibrium `x*` of the game is a fixed point of
the proximal best-response map, `x*_i = x̂_i(x*)` for every player `i`. -/
theorem fixed_point
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs) :
    ∀ i : Fin N, xhat xs i = xs i := by sorry

end LeiBR.Sync
