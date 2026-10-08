-- Prove2me | Theorems.Thm_LeiBR_Rand_eq9_contraction
-- name    : LeiBR.Rand.eq9_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:38.37032+00:00
-- url     : https://prove2.me/theorems/8aa3184e-c752-4451-9092-c8e0318489de
-- title:
--   (9) — under $\|\Gamma\| < 1$ the proximal BR map contracts with factor $a$
-- statement:
--   Let Assumptions 1 and 2 hold, $\mu > 0$, and $a = \|\Gamma\|$. For all $y, y' \in X$,
--   $$\Big(\sum_{i=1}^N \|\widehat x_i(y') - \widehat x_i(y)\|^2\Big)^{1/2} \le a\,\Big(\sum_{i=1}^N \|y'_i - y_i\|^2\Big)^{1/2}.$$
--
--   Since $a < 1$, the proximal best-response map is a contraction of $X$ in the Euclidean norm of the vector of block norms; its unique fixed point is the Nash equilibrium.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 7, §3.2, (9)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (9), §3.2, p. 7: under Assumption 2, with `a = ‖Γ‖`,
`‖(‖x̂_i(y') − x̂_i(y)‖)_i‖ ≤ a ‖(‖y'_i − y_i‖)_i‖` for all `y, y' ∈ X`. -/
theorem eq9_contraction {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (y y' : LeiBR.Sync.Profile n) (hy : G.Feasible y) (hy' : G.Feasible y') :
    blockNorm (xhat y' - xhat y) ≤ contrFactor G mu * blockNorm (y' - y) := by sorry

end LeiBR.Rand
