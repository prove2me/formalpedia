-- Prove2me | Theorems.Thm_HolisticService_Effort_utilde_hasDerivAt
-- name    : HolisticService.Effort.utilde_hasDerivAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:41.806616+00:00
-- url     : https://prove2.me/theorems/6c94025c-9059-4897-a4e8-ee618c3b2e1c
-- title:
--   Proof of Proposition 1, p. 27 — the partial derivative ∂Ũ/∂δᵢ = (1 − c̃ᵢ)(Vᴴᵢ − Vᴸᵢ) − r(σᴴᵢ − σᴸᵢ) Σⱼ (δⱼ(σᴴⱼ − σᴸⱼ) + σᴸⱼ)ρᵢⱼ
-- statement:
--   Assume the standing assumptions of the service design model. For every effort vector $\delta$ and step $i$, the partial derivative of $\tilde{\mathcal U}$ in $\delta_i$ (all other efforts fixed) is
--   $$\frac{\partial\tilde{\mathcal U}(\delta)}{\partial\delta_i} = \Big(1-\big(c_i-\textstyle\sum_{m\ne i}\beta_{i,m}\big)\Big)(V^H_i-V^L_i) - r(\sigma^H_i-\sigma^L_i)\sum_{j=1}^n\big(\delta_j(\sigma^H_j-\sigma^L_j)+\sigma^L_j\big)\rho_{i,j},$$
--   with $\rho_{i,i} = 1$.
--
--   These are the first-order conditions the paper solves to obtain the closed form $\hat\delta$.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 27 (PDF 27), proof of Proposition 1, ∂Ũ(δ)/∂δ_i

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 27: the partial derivative of `Ũ` in `δ_i` is
`(1 − (c_i − Σ_{m≠i} β_{i,m}))(V^H_i − V^L_i) − r(σ^H_i − σ^L_i) Σ_j (δ_j(σ^H_j − σ^L_j) + σ^L_j)ρ_{i,j}`. -/
theorem utilde_hasDerivAt {n : ℕ} (M : Params n) (hS : M.Standing) (δ : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => Utilde M (Function.update δ i t)) (gradU M δ i) (δ i) := by sorry

end HolisticService.Effort
