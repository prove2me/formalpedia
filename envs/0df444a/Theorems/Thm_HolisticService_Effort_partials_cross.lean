-- Prove2me | Theorems.Thm_HolisticService_Effort_partials_cross
-- name    : HolisticService.Effort.partials_cross
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:48.575481+00:00
-- url     : https://prove2.me/theorems/1efb9e59-6625-4337-bc3a-87184a02e0b6
-- title:
--   Proof of Proposition 3, p. 28 — the cross partials ∂δ*ᵢ/∂Vᴴⱼ, ∂δ*ᵢ/∂cⱼ, ∂δ*ᵢ/∂σᴴⱼ for j ≠ i
-- statement:
--   Assume the standing assumptions, no technical coupling ($\beta_{j,i} = 0$ for $j \ne i$) and the interior condition, and let $\delta^*$ be the optimal effort of the design problem, viewed as a function of one parameter of step $j$ at a time (all others fixed). For steps $i \ne j$, at the given parameters,
--   $$\frac{\partial\delta^*_i}{\partial V^H_j} = \frac{1-c_j}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{i,j},\qquad \frac{\partial\delta^*_i}{\partial c_j} = -\frac{V^H_j-V^L_j}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{j,i},$$
--   $$\frac{\partial\delta^*_i}{\partial\sigma^H_j} = -\frac{(1-c_j)(V^H_j-V^L_j)}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)^2}[\mathbf P^{-1}]_{j,i}.$$
--
--   The sign of each cross derivative is the product of the sign of $(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)$ (whether the steps are of the same type) and the sign of $[\mathbf P^{-1}]_{i,j}$, which is the content of Proposition 3.
--
--   **Formalization Note** The orientation is the page's: the effort at step $i$ is differentiated in a parameter of step $j$. $V^H_j$ moves with $V^L_j$ fixed and $\sigma^H_j$ with $\sigma^L_j$ fixed.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 28 (PDF 28), proof of Proposition 3, ∂δ*_i/∂V^H_j, ∂δ*_i/∂c_j, ∂δ*_i/∂σ^H_j

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 3, p. 28 (cross steps), with no technical coupling (p. 14): for `j ≠ i`,
the partial derivatives of the optimal effort `δ*_i` in `V^H_j`, `c_j` and `σ^H_j`. -/
theorem partials_cross {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i j : Fin n) (hij : i ≠ j) :
    HasDerivAt (fun t => optEffort (withVH M j t) i)
        ((1 - M.c j) / (M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j)) * M.P⁻¹ i j) (M.VH j) ∧
      HasDerivAt (fun t => optEffort (withC M j t) i)
        (-(M.VH j - M.VL j) / (M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j)) * M.P⁻¹ j i) (M.c j) ∧
      HasDerivAt (fun t => optEffort (withSH M j t) i)
        (-((1 - M.c j) * (M.VH j - M.VL j)) / (M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j) ^ 2)
          * M.P⁻¹ j i) (M.sH j) := by sorry

end HolisticService.Effort
