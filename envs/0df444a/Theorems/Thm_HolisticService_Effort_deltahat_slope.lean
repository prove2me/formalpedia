-- Prove2me | Theorems.Thm_HolisticService_Effort_deltahat_slope
-- name    : HolisticService.Effort.deltahat_slope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:44.143573+00:00
-- url     : https://prove2.me/theorems/1f93faae-a230-4708-adc2-3bc514384e38
-- title:
--   Proof of Proposition 1, p. 27 — ∂δ̂ᵢ/∂(Vᴴᵢ − Vᴸᵢ) = (1 − c̃ᵢ)|P[−i;−i]| / (r(σᴴᵢ − σᴸᵢ)²|P|) > 0
-- statement:
--   Assume the standing assumptions of the service design model and fix a step $i$. As a function of $V^H_i$, with every other parameter (in particular $V^L_i$) fixed, the closed form $\hat\delta_i$ is differentiable with
--   $$\frac{\partial\hat\delta_i}{\partial(V^H_i-V^L_i)} = \frac{\big(1-(c_i-\sum_{m\ne i}\beta_{i,m})\big)|\mathbf P[-i;-i]|}{r(\sigma^H_i-\sigma^L_i)^2|\mathbf P|} > 0,$$
--   where $\mathbf P[-i;-i]$ is $\mathbf P$ with row and column $i$ removed.
--
--   The positive slope is what turns the conditions $\hat\delta_i \le 0$ and $\hat\delta_i \ge 1$ into thresholds on $V^H_i - V^L_i$.
--
--   **Formalization Note** $|\mathbf P[-i;-i]|$ is `adjugate P i i`. Since $V^L_i$ is fixed, differentiating in $V^H_i$ is differentiating in $V^H_i - V^L_i$.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 27 (PDF 27), proof of Proposition 1, ∂δ̂_i/∂(V^H_i − V^L_i)

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 27: `∂δ̂_i/∂(V^H_i − V^L_i) = (1 − (c_i − Σ_{m≠i} β_{i,m}))|P[−i;−i]| /
(r(σ^H_i − σ^L_i)²|P|) > 0`; `V^H_i` moves with `V^L_i` fixed, and `|P[−i;−i]|` is `adjugate P i i`. -/
theorem deltahat_slope {n : ℕ} (M : Params n) (hS : M.Standing) (i : Fin n) :
    HasDerivAt (fun t => δhat (withVH M i t) i)
        ((1 - ctil M i) * M.P.adjugate i i / (M.r * (M.sH i - M.sL i) ^ 2 * M.P.det)) (M.VH i) ∧
      0 < (1 - ctil M i) * M.P.adjugate i i / (M.r * (M.sH i - M.sL i) ^ 2 * M.P.det) := by sorry

end HolisticService.Effort
