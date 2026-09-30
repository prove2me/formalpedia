-- Prove2me | Theorems.Thm_GoldenRatioVI_Explicit_zbar_identity
-- name    : GoldenRatioVI.Explicit.zbar_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:30:21.880024+00:00
-- url     : https://prove2.me/theorems/33a52a46-3142-4cc3-a914-ea2dc3e39685
-- title:
--   Eq. (24) — identity linking $z^{k+1}$, $\bar z^{k+1}$ and $\bar z^k$
-- statement:
--   Consider a run of Algorithm 1 (EGRAAL) with parameter $\phi\in(1,\varphi]$ and iterates $(z^k)$, $(\bar z^k)$. For every point $z\in\mathcal E$ and every $k\ge 0$,
--   $$\|z^{k+1}-z\|^2 = \frac{\phi}{\phi-1}\|\bar z^{k+1}-z\|^2 - \frac1{\phi-1}\|\bar z^k-z\|^2 + \frac1\phi\|z^{k+1}-\bar z^k\|^2. \tag{24}$$
--
--   The identity follows from the averaging step (16) and lets the analysis measure progress through the averaged iterates $\bar z^k$.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 6, Eq. (24)

import Mathlib
import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

namespace GoldenRatioVI.Explicit

/-- Eq. (24) of Malitsky (p. 6): along a run of Algorithm 1, for every point `z` of `E` and
every `k ≥ 0`,
`‖z^{k+1} − z‖² = (ϕ/(ϕ−1))‖z̄^{k+1} − z‖² − (1/(ϕ−1))‖z̄^k − z‖² + (1/ϕ)‖z^{k+1} − z̄^k‖²`. -/
theorem zbar_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (u : E) (k : ℕ) :
    ‖z (k + 1) - u‖ ^ 2 =
      ϕ / (ϕ - 1) * ‖zbar (k + 1) - u‖ ^ 2 - 1 / (ϕ - 1) * ‖zbar k - u‖ ^ 2
        + 1 / ϕ * ‖z (k + 1) - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Explicit
