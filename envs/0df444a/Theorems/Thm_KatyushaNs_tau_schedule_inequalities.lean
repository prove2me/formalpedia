-- Prove2me | Theorems.Thm_KatyushaNs_tau_schedule_inequalities
-- name    : KatyushaNs.tau_schedule_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:54.42117+00:00
-- url     : https://prove2.me/theorems/4bf34126-2713-42d4-9bc4-e1ed6dc30cf7
-- title:
--   Proof of Theorem 4.1, p. 27: inequalities of the schedule $\tau_{1,s} = 2/(s+4)$
-- statement:
--   Let $\tau_{1,s} = \frac{2}{s+4}$ for $s = 0, 1, 2, \dots$ and $\tau_2 = \frac12$. Then for every $s \ge 0$:
--
--   1. $\tau_{1,s} \le \frac12$;
--   2. $\displaystyle \frac{1}{\tau_{1,s}^2} \ge \frac{1 - \tau_{1,s+1}}{\tau_{1,s+1}^2}$;
--   3. $\displaystyle \frac{\tau_{1,s}+\tau_2}{\tau_{1,s}^2} \ge \frac{\tau_2}{\tau_{1,s+1}^2}$.
--
--   These two inequalities let the recursions (C.3) and (C.2) be chained over all epochs.
--
--   Differences from the source: none.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), unnumbered display, p. 27

import Mathlib
import Definitions.Def_KatyushaNs_tau1

namespace KatyushaNs

/-- **The two inequalities satisfied by `τ_{1,s} = 2/(s+4)`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), unnumbered display, p. 27 (PDF p. 28):
"At this point, if we choose τ_{1,s} = 2/(s+4) ≤ 1/2, it satisfies
1/τ²_{1,s} ≥ (1 − τ_{1,s+1})/τ²_{1,s+1} and (τ_{1,s} + τ₂)/τ²_{1,s} ≥ τ₂/τ²_{1,s+1}."

Conclusion: for every epoch `s ≥ 0`, with `τ₂ = 1/2`: `τ_{1,s} ≤ 1/2`,
`(1 − τ_{1,s+1})/τ²_{1,s+1} ≤ 1/τ²_{1,s}` and `τ₂/τ²_{1,s+1} ≤ (τ_{1,s} + τ₂)/τ²_{1,s}`.

**Formalization Note.** `τ₂ = 1/2` (Algorithm 2, line 2) is written as `1/2`. -/
theorem tau_schedule_inequalities (s : ℕ) :
    tau1 s ≤ 1 / 2 ∧
      (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ≤ 1 / tau1 s ^ 2 ∧
      (1 / 2) / tau1 (s + 1) ^ 2 ≤ (tau1 s + 1 / 2) / tau1 s ^ 2 := by sorry

end KatyushaNs
