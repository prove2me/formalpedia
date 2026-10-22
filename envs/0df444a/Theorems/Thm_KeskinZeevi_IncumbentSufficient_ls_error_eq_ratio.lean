-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_ls_error_eq_ratio
-- name    : KeskinZeevi.IncumbentSufficient.ls_error_eq_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:45:15.17122+00:00
-- url     : https://prove2.me/theorems/bedd8b6e-5dd2-4736-b362-46136f50dd1b
-- title:
--   (27) — least squares error equals M_t / Ĵ_t
-- statement:
--   Fix any pricing policy, any slope $\beta$, any realization of the shocks and any period $t$. If the information metric $\hat J_t = \sum_{s=1}^t x_s^2$ is nonzero, then the least squares error is a ratio of the noise sum to the information:
--   $$\hat\beta_t - \beta = \frac{M_t}{\hat J_t}, \qquad M_t = \sum_{s=1}^t \varepsilon_s x_s .$$
--   This follows from the demand equation $D_s - \hat D = \beta x_s + \varepsilon_s$. It reduces the estimation error to a self-normalized martingale, which Lemma 5 then controls.
--
--   **Formalization Note.** The paper writes the identity "for all $t = 1, 2, \dots$". It is meaningful only when $\hat J_t \ne 0$, since otherwise $\hat\beta_t$ is undefined, so the Lean statement assumes $\hat J_t \ne 0$ (this implies $t \ge 1$). The identity is pathwise; no probabilistic hypothesis is needed.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1150, Eq. (27)

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1150, (27): along any price path of any policy, whenever
`Ĵ_t = Σ_{s=1}^t x_s² ≠ 0`, the least squares error is `β̂_t - β = M_t / Ĵ_t` with
`M_t = Σ_{s=1}^t ε_s x_s`. -/
theorem ls_error_eq_ratio (M : Model) {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (hJ : Jhat π β ε t ω ≠ 0) :
    betaHat π β ε t ω - β = noiseSum π β ε t ω / Jhat π β ε t ω := by sorry

end KeskinZeevi.IncumbentSufficient
