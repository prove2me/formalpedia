-- Prove2me | Theorems.Thm_LeiBR_Rand_prox_br_fixed_point
-- name    : LeiBR.Rand.prox_br_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:49.802085+00:00
-- url     : https://prove2.me/theorems/b4678c2c-ea69-4c50-8508-347ae4cd1374
-- title:
--   Proof of Proposition 2 — a Nash equilibrium is a fixed point of the proximal BR map
-- statement:
--   Let Assumption 1 hold, $\mu > 0$, and let $x^*$ be a Nash equilibrium of the game. Then for every player $i$,
--   $$\widehat x_i(x^*) = x_i^*.$$
--
--   The convergence analyses compare the iterates with the exact best responses and use this identity to center them at the equilibrium.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 7, §3.2, proof of Proposition 2

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- §3.2, proof of Proposition 2, p. 7: a Nash equilibrium `x*` is a fixed point of the proximal
BR map, `x*_i = x̂_i(x*)` for every `i`. -/
theorem prox_br_fixed_point {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (i : Fin N) :
    xhat xstar i = xstar i := by sorry

end LeiBR.Rand
