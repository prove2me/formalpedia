-- Prove2me | Theorems.Thm_LeiBR_Rand_eq5_gamma_contraction
-- name    : LeiBR.Rand.eq5_gamma_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:45.745642+00:00
-- url     : https://prove2.me/theorems/5b103559-5b5d-4563-bc2e-da2631742972
-- title:
--   (5) — the proximal BR map is a $\Gamma$-contraction blockwise
-- statement:
--   Let Assumption 1 hold and $\mu > 0$, and let $\widehat x$ be the proximal best-response map (2). For all profiles $y, y' \in X$ and every player $i$,
--   $$\|\widehat x_i(y') - \widehat x_i(y)\| \le \sum_{j=1}^N \gamma_{ij}\,\|y'_j - y_j\|,$$
--   with $\Gamma = [\gamma_{ij}]$ the matrix (3). In vector form, $(\|\widehat x_i(y') - \widehat x_i(y)\|)_{i} \le \Gamma\,(\|y'_i - y_i\|)_i$ componentwise.
--
--   This is the basic contraction estimate behind all three schemes of the paper: a player's proximal best response moves at most by the $\Gamma$-weighted moves of all strategies.
--
--   **Formalization Note** The paper obtains (5) by adapting [19, Section 12.6.1] and does not prove it; it needs the joint $C^2$ regularity recorded in Assumption 1.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 5, §2.2, (5)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (5), §2.2, p. 5: the proximal BR map is a `Γ`-contraction blockwise:
`‖x̂_i(y') − x̂_i(y)‖ ≤ ∑_j γ_ij ‖y'_j − y_j‖` for all `y, y' ∈ X`. -/
theorem eq5_gamma_contraction {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (y y' : LeiBR.Sync.Profile n) (hy : G.Feasible y) (hy' : G.Feasible y') (i : Fin N) :
    ‖xhat y' i - xhat y i‖ ≤ ∑ j, Gamma G mu i j * ‖y' j - y j‖ := by sorry

end LeiBR.Rand
