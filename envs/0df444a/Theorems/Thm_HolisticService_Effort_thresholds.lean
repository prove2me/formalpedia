-- Prove2me | Theorems.Thm_HolisticService_Effort_thresholds
-- name    : HolisticService.Effort.thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:43.085135+00:00
-- url     : https://prove2.me/theorems/26b802ba-c42f-4355-9e4f-27b3d2047b82
-- title:
--   Proof of Proposition 1, p. 27 — δ̂ᵢ ≤ 0 iff Vᴴᵢ − Vᴸᵢ ≤ ΔV̲ᵢ, δ̂ᵢ ≥ 1 iff Vᴴᵢ − Vᴸᵢ ≥ ΔV̄ᵢ, ΔV̄ᵢ − ΔV̲ᵢ > 0, so the interior condition gives δ̂ ∈ (0,1)ⁿ
-- statement:
--   Assume the standing assumptions of the service design model, and let $\underline{\Delta V}_i$, $\overline{\Delta V}_i$ be the thresholds printed on p. 27. Then for every step $i$:
--
--   1. $\hat\delta_i \le 0$ if and only if $V^H_i - V^L_i \le \underline{\Delta V}_i$;
--   2. $\hat\delta_i \ge 1$ if and only if $V^H_i - V^L_i \ge \overline{\Delta V}_i$;
--   3. the gap between the thresholds is
--   $$\overline{\Delta V}_i - \underline{\Delta V}_i = \frac{r(\sigma^H_i-\sigma^L_i)^2|\mathbf P|}{\big(1-(c_i-\sum_{m\ne i}\beta_{i,m})\big)|\mathbf P[-i;-i]|} > 0.$$
--
--   Consequently the interior condition, $V^H_i - V^L_i \in (\underline{\Delta V}_i, \overline{\Delta V}_i)$ for all $i$, holds if and only if $\hat\delta_i \in (0,1)$ for all $i$.
--
--   The thresholds are the paper's standing hypothesis for the whole of §4; this statement connects them to the closed form.
--
--   **Formalization Note** The page states "ensures that $\hat\delta_i \in (0,1)$"; the converse follows from items 1–2 and is included. The thresholds are defined by their explicit formulas, with $(-1)^{i+j}|\mathbf P[-j;-i]|$ written `adjugate P i j`.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 27 (PDF 27), proof of Proposition 1, thresholds ΔV_i and ΔV̄_i

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 27: `δ̂_i ≤ 0` iff `V^H_i − V^L_i ≤ ΔV_i`, `δ̂_i ≥ 1` iff
`V^H_i − V^L_i ≥ ΔV̄_i`, `ΔV̄_i − ΔV_i = r(σ^H_i − σ^L_i)²|P| / ((1 − (c_i − Σ_{m≠i} β_{i,m}))|P[−i;−i]|) > 0`;
hence the interior condition is exactly `δ̂ ∈ (0,1)^n`. -/
theorem thresholds {n : ℕ} (M : Params n) (hS : M.Standing) :
    (∀ i : Fin n,
      (δhat M i ≤ 0 ↔ M.VH i - M.VL i ≤ ΔVlo M i) ∧
      (1 ≤ δhat M i ↔ ΔVhi M i ≤ M.VH i - M.VL i) ∧
      ΔVhi M i - ΔVlo M i
          = M.r * (M.sH i - M.sL i) ^ 2 * M.P.det / ((1 - ctil M i) * M.P.adjugate i i) ∧
      0 < ΔVhi M i - ΔVlo M i) ∧
    (Interior M ↔ ∀ i, 0 < δhat M i ∧ δhat M i < 1) := by sorry

end HolisticService.Effort
