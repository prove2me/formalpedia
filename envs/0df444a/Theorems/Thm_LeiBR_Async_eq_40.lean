-- Prove2me | Theorems.Thm_LeiBR_Async_eq_40
-- name    : LeiBR.Async.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:39.983964+00:00
-- url     : https://prove2.me/theorems/794aa625-1487-4a5e-86f0-dd0b236229c4
-- title:
--   (40) — $\mathbb E\|\hat x_i(y) - x^*_i\| \le a_\infty \max_j \mathbb E\|y_j - x^*_j\|$ for a random profile $y$
-- statement:
--   Let Assumption 1(a)–(b) hold, let $\mu > 0$, let $\hat x$ be the proximal best-response map and $x^*$ a Nash equilibrium. Let $y : \Omega \to X$ be a measurable random profile on a probability space $(\Omega, \mathcal F, \mathbb P)$. Then for every player $i$,
--   $$\mathbb E\big[\|\hat x_i(y) - x^*_i\|\big] = \mathbb E\big[\|\hat x_i(y) - \hat x_i(x^*)\|\big] \le a_\infty \max_{j} \mathbb E\big[\|y_j - x^*_j\|\big],$$
--   where $a_\infty = \|\Gamma\|_\infty$.
--
--   This is the expected-value, $\infty$-norm form of the contraction (5); it controls the exact best response to outdated information in the asynchronous scheme.
--
--   **Formalization Note** Assumption 5 is not needed for this inequality and is not assumed.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 18, §5.1, (40)

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

namespace LeiBR.Async

open MeasureTheory

/-- Inequality (40) (§5.1, p. 18): for a random profile `y : Ω → X` and every player `i`,
`E‖x̂_i(y) − x*_i‖ = E‖x̂_i(y) − x̂_i(x*)‖ ≤ a_∞ max_j E‖y_j − x*_j‖`, where `a_∞ = ‖Γ‖_∞`. -/
theorem eq_40 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n) (hNE : LeiBR.Sync.IsNashEq X f xs)
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable y) (hyX : ∀ ω, y ω ∈ profileSet X) (i : Fin N) :
    ∫ ω, ‖xhat (y ω) i - xs i‖ ∂P = ∫ ω, ‖xhat (y ω) i - xhat xs i‖ ∂P ∧
      ∫ ω, ‖xhat (y ω) i - xhat xs i‖ ∂P ≤
        normInf (LeiBR.Sync.Gamma X f μ) * ⨆ j, ∫ ω, ‖y ω j - xs j‖ ∂P := by sorry

end LeiBR.Async
