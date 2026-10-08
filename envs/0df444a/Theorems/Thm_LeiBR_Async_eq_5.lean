-- Prove2me | Theorems.Thm_LeiBR_Async_eq_5
-- name    : LeiBR.Async.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:34.341216+00:00
-- url     : https://prove2.me/theorems/32848e9f-86d9-449e-92b3-25b9903cae61
-- title:
--   (5) — the proximal BR map is a $\Gamma$-contraction blockwise
-- statement:
--   Let Assumption 1(a)–(b) hold, let $\mu > 0$, and let $\hat x$ be the proximal best-response map. Then for all profiles $y, y' \in X$ and every player $i$,
--   $$\|\hat x_i(y') - \hat x_i(y)\| \le \sum_{j=1}^N \gamma_{ij}\,\|y'_j - y_j\| ,$$
--   that is, the vector of blockwise distances $\big(\|\hat x_i(y') - \hat x_i(y)\|\big)_i$ is bounded componentwise by $\Gamma$ applied to $\big(\|y'_j - y_j\|\big)_j$.
--
--   This is the basic contraction property of the proximal best response on which every convergence statement of the paper rests; combined with the $\infty$-norm bound on $\Gamma$ it gives (40).
--
--   **Formalization Note** The paper obtains (5) by modifying a proof in Facchinei and Pang; it is stated here under Assumption 1(a)–(b), which includes the joint $C^2$ regularity that the mixed Hessian blocks in $\Gamma$ require.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 5, §2.2, (5)

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

namespace LeiBR.Async

/-- Inequality (5) (Lei, Shanbhag, Pang & Sen, arXiv:1704.04578v2, §2.2, p. 5): the proximal BR map is
a `Γ`-contraction blockwise. For `y, y' ∈ X` and every player `i`,
`‖x̂_i(y') − x̂_i(y)‖ ≤ Σ_j γ_ij ‖y'_j − y_j‖`. -/
theorem eq_5 {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) :
    ∀ y ∈ profileSet X, ∀ y' ∈ profileSet X, ∀ i : Fin N,
      ‖xhat y' i - xhat y i‖ ≤ ∑ j, LeiBR.Sync.Gamma X f μ i j * ‖y' j - y j‖ := by sorry

end LeiBR.Async
