-- Prove2me | Theorems.Thm_LeiBR_Async_normInf_Gamma_lt_one
-- name    : LeiBR.Async.normInf_Gamma_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:59.091981+00:00
-- url     : https://prove2.me/theorems/2b38ac86-2be8-4df4-b4f6-36e285144a94
-- title:
--   §5.1 — strict diagonal dominance gives $a_\infty = \|\Gamma\|_\infty < 1$
-- statement:
--   Let $\mu > 0$ and suppose Assumption 5 holds: $\zeta_{i,\min} > \sum_{j\neq i}\zeta_{ij,\max}$ for every player $i$. Then the matrix $\Gamma$ of (3) satisfies
--   $$a_\infty = \|\Gamma\|_\infty = \max_i \sum_{j} |\gamma_{ij}| < 1 .$$
--
--   This is the contraction modulus of the best-response map in the $\infty$-norm used by the asynchronous analysis; it enters the rate $\rho$ of Lemma 7.
--
--   **Formalization Note** Only $\mu > 0$ and Assumption 5 are assumed; the curvature constants are those of the model definition.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 18, §5.1, sentence after Assumption 5

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

namespace LeiBR.Async

/-- Under strict diagonal dominance (Assumption 5), `a_∞ = ‖Γ‖_∞ < 1` (§5.1, sentence after
Assumption 5, p. 18). -/
theorem normInf_Gamma_lt_one {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (μ : ℝ) (hμ : 0 < μ) (hA5 : Assumption5 X f) :
    normInf (LeiBR.Sync.Gamma X f μ) < 1 := by sorry

end LeiBR.Async
