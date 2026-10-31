-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_ons_beta_inv_bound
-- name    : LogRegretOCO.ONS.ons_beta_inv_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:58.124025+00:00
-- url     : https://prove2.me/theorems/6f6ad525-1757-4d56-916c-3330d5280244
-- title:
--   Proof of Theorem 2 — $1/\beta \le 8(GD + 1/\alpha)$
-- statement:
--   Let $G, D, \alpha > 0$ and $\beta = \tfrac12\min\{\tfrac{1}{4GD}, \alpha\}$. Then
--   $$
--   \frac{1}{\beta} \le 8\Bigl(GD + \frac{1}{\alpha}\Bigr).
--   $$
--   This converts the regret bound $\tfrac{n}{2\beta}\log T + \tfrac{1}{2\beta}$ into one in terms of the problem constants $G$, $D$ and $\alpha$.
--
--   Differences from the source:
--   - encoding: G, D positive implicitly (1/(4GD)); α > 0 standing (p. 173) → hypotheses 0 < G, 0 < D, 0 < α; reason: the conditions only exclude the cases in which β is undefined; α > 0 is the paper's own standing assumption
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, proof of Theorem 2, last paragraph, p. 179 (PDF p. 11)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta

namespace LogRegretOCO.ONS

/-- **The constant `1/β ≤ 8(GD + 1/α)` (proof of Theorem 2).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, proof of Theorem 2, p. 179:
"Since β = 1/2 min{1/(4GD), α}, we have 1/β ≤ 8(GD + 1/α)."

**Formalization Note.** `G, D, α > 0` (the standing assumptions; `1/(4GD)` is otherwise
undefined). -/
theorem ons_beta_inv_bound {G D α : ℝ} (hG : 0 < G) (hD : 0 < D) (hα : 0 < α) :
    1 / onsBeta G D α ≤ 8 * (G * D + 1 / α) := by sorry

end LogRegretOCO.ONS
