-- Prove2me | Theorems.Thm_HolisticService_Effort_foc_iff_deltahat
-- name    : HolisticService.Effort.foc_iff_deltahat
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:49.114655+00:00
-- url     : https://prove2.me/theorems/14ffbe0a-cbf4-454d-aebb-bb18d7bbf061
-- title:
--   Proof of Proposition 1, p. 27 — the first-order conditions ∂Ũ/∂δ₁ = … = ∂Ũ/∂δₙ = 0 have the unique solution δ̂
-- statement:
--   Assume the standing assumptions of the service design model, and let $g_i(\delta)$ be the partial derivative of $\tilde{\mathcal U}$ in $\delta_i$ as printed on p. 27. For every $\delta \in \mathbb R^n$,
--   $$g_1(\delta) = \dots = g_n(\delta) = 0 \iff \delta = \hat\delta,$$
--   where
--   $$\hat\delta_i = \sum_{j=1}^n \frac{\big(1-(c_j-\sum_{m\ne j}\beta_{j,m})\big)(V^H_j-V^L_j)}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{i,j} - \frac{\sigma^L_i}{\sigma^H_i-\sigma^L_i}.$$
--
--   This is the closed form of Proposition 1; whether it is the optimum depends on its lying in the box, which the interior condition guarantees.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 27 (PDF 27), proof of Proposition 1, δ̂_i

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 27: the system of first-order conditions
`∂Ũ/∂δ_1 = 0, …, ∂Ũ/∂δ_n = 0` has the unique solution `δ̂`. -/
theorem foc_iff_deltahat {n : ℕ} (M : Params n) (hS : M.Standing) (δ : Fin n → ℝ) :
    (∀ i, gradU M δ i = 0) ↔ δ = δhat M := by sorry

end HolisticService.Effort
