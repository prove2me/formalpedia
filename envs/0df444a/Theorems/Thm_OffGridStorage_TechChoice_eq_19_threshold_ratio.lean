-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_eq_19_threshold_ratio
-- name    : OffGridStorage.TechChoice.eq_19_threshold_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:00.034385+00:00
-- url     : https://prove2.me/theorems/497bb8ba-6348-489d-98fb-70338c1516c2
-- title:
--   A.2, eq. (19), p. 37 — g = g0 iff c_K/e = g − √(2c_Q g), and g > g0 iff c_K/e < g − √(2c_Q g)
-- statement:
--   Let $c_Q>0$, $r\ge 0$ and $g>2c_Q$, and write $g_0(c_Q,r)=c_Q+r+\sqrt{c_Q^2+2c_Qr}$. Then
--
--   $$g_0(c_Q,r)=g\iff r=g-\sqrt{2c_Qg},\qquad g_0(c_Q,r)<g\iff r<g-\sqrt{2c_Qg}.$$
--
--   With $r=c_K/e$ the first equivalence is eq. (19): solving $g=g_0$ for the cost-to-efficiency ratio. The second is the form in which the proof of Theorem 2 uses it: a technology is profitable at backup cost $g$ exactly when its ratio lies below $g-\sqrt{2c_Qg}$.
--
--   **Formalization Note** Eq. (19) is printed as a chain of equalities at the boundary $g=g_0$; the strict version is the one the surrounding prose relies on ("a lower $g_0$ means that the range of back-up costs for which the technology is suitable … is larger").
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 37, Appendix A.2 (proof of Theorem 2), eq. (19)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- A.2, eq. (19), p. 37: with `r = c_K/e`, the backup cost equals the threshold exactly when
`r = g - √(2 c_Q g)`, and exceeds it exactly when `r < g - √(2 c_Q g)`. -/
theorem eq_19_threshold_ratio (cQ r g : ℝ) (hcQ : 0 < cQ) (hr : 0 ≤ r) (hg : 2 * cQ < g) :
    (g0ratio cQ r = g ↔ r = g - Real.sqrt (2 * cQ * g)) ∧
    (g0ratio cQ r < g ↔ r < g - Real.sqrt (2 * cQ * g)) := by sorry

end OffGridStorage.TechChoice
