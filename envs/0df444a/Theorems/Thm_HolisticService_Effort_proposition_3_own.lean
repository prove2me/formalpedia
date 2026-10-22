-- Prove2me | Theorems.Thm_HolisticService_Effort_proposition_3_own
-- name    : HolisticService.Effort.proposition_3_own
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:48.866978+00:00
-- url     : https://prove2.me/theorems/286a4b31-fa41-4fc7-ad95-68d7df587f51
-- title:
--   Proposition 3, p. 16, first sentence — ∂δ*ᵢ/∂cᵢ < 0, ∂δ*ᵢ/∂Vᴴᵢ > 0, and ∂δ*ᵢ/∂σᴴᵢ has the sign opposite to σᴴᵢ − σᴸᵢ
-- statement:
--   Assume the standing assumptions, no technical coupling and the interior condition, and let $\delta^*$ be the optimal effort of the design problem. For every step $i$, at the given parameters,
--
--   1. $\partial\delta^*_i/\partial c_i < 0$;
--   2. $\partial\delta^*_i/\partial V^H_i > 0$;
--   3. $\partial\delta^*_i/\partial\sigma^H_i > 0$ when $\sigma^H_i - \sigma^L_i < 0$ (a routine step), and
--   4. $\partial\delta^*_i/\partial\sigma^H_i < 0$ when $\sigma^H_i - \sigma^L_i > 0$ (a non-routine step).
--
--   A costlier step receives less effort and a step with a higher attainable functional value more; a larger $\sigma^H_i$ lowers the effort at a non-routine step and raises it at a routine one.
--
--   **Formalization Note** Each derivative is the ordinary derivative of the optimal effort along one parameter at the given point ($V^H_i$ with $V^L_i$ fixed, $\sigma^H_i$ with $\sigma^L_i$ fixed). A strict sign of the derivative also asserts differentiability, since an undefined derivative is $0$ in Lean.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 16 (PDF 16), Proposition 3, first sentence

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proposition 3, p. 16, first sentence: `∂δ*_i/∂c_i < 0`, `∂δ*_i/∂V^H_i > 0`, and
`∂δ*_i/∂σ^H_i > 0` when `σ^H_i − σ^L_i < 0`, `∂δ*_i/∂σ^H_i < 0` when `σ^H_i − σ^L_i > 0`. -/
theorem proposition_3_own {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i : Fin n) :
    deriv (fun t => optEffort (withC M i t) i) (M.c i) < 0 ∧
      0 < deriv (fun t => optEffort (withVH M i t) i) (M.VH i) ∧
      (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) i) (M.sH i)) ∧
      (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) i) (M.sH i) < 0) := by sorry

end HolisticService.Effort
