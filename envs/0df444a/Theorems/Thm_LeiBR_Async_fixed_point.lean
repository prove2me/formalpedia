-- Prove2me | Theorems.Thm_LeiBR_Async_fixed_point
-- name    : LeiBR.Async.fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:11.405104+00:00
-- url     : https://prove2.me/theorems/dc0048c1-d41d-4788-961f-81d9feae5057
-- title:
--   Proof of Proposition 2 — a Nash equilibrium is a fixed point of the proximal BR map
-- statement:
--   Let Assumption 1(a)–(b) hold, let $\mu > 0$, let $\hat x$ be the proximal best-response map, and let $x^*$ be a Nash equilibrium. Then for every player $i$,
--   $$x^*_i = \hat x_i(x^*).$$
--
--   This identity is what turns the contraction (5) of the best-response map into a contraction towards the equilibrium; it is used in (40) and throughout the rate analysis.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 7, §3.2, proof of Proposition 2

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

namespace LeiBR.Async

/-- A Nash equilibrium is a fixed point of the proximal BR map, `x*_i = x̂_i(x*)` (§3.2, proof of
Proposition 2, p. 7). -/
theorem fixed_point {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n)
    (hNE : LeiBR.Sync.IsNashEq X f xs) :
    ∀ i : Fin N, xhat xs i = xs i := by sorry

end LeiBR.Async
