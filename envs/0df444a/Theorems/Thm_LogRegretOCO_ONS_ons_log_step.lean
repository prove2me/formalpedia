-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_ons_log_step
-- name    : LogRegretOCO.ONS.ons_log_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:25.142509+00:00
-- url     : https://prove2.me/theorems/69ac9ba6-390c-4164-b6cd-0d7ae16d273a
-- title:
--   Proof of Theorem 2 — $\log(TG^2\beta^2D^2 + 1) \le \log T$ (corrected: $T \ge 2$)
-- statement:
--   Let $G, D, \alpha > 0$, let $\beta = \tfrac12\min\{\tfrac{1}{4GD}, \alpha\}$ and let $n \in \mathbb N$. Then for every integer $T \ge 2$,
--   $$
--   \frac{n}{2\beta}\log\bigl(T G^2 \beta^2 D^2 + 1\bigr) \le \frac{n}{2\beta}\log T .
--   $$
--   This is the last step of the potential bound in the proof of Theorem 2; it rests on $G\beta D \le \tfrac18$.
--
--   Differences from the source:
--   - correction: (n/2β) log(TG²β²D² + 1) ≤ (n/2β) log(T) for every T → for every T ≥ 2; reason: at T = 1 the right side is (n/2β) log 1 = 0 while the left side is (n/2β) log(G²β²D² + 1) > 0 for every n ≥ 1 and G, D, α > 0 (e.g. n = G = D = α = 1, β = 1/8: left side 4 log(65/64) > 0); for T ≥ 2 it holds since G²β²D² ≤ 1/64
--   - encoding: G, D positive implicitly (1/(4GD)); α > 0 standing (p. 173) → hypotheses 0 < G, 0 < D, 0 < α; reason: the conditions only exclude the cases in which β is undefined; α > 0 is the paper's own standing assumption
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, proof of Theorem 2, last line of the unnumbered display, p. 179 (PDF p. 11)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta

namespace LogRegretOCO.ONS

/-- **The last logarithmic step (proof of Theorem 2; corrected: T ≥ 2).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, proof of Theorem 2, last line of the unnumbered display, p. 179:
"≤ (n/2β) log(TG²β²D² + 1) ≤ (n/2β) log(T)."

For `G, D, α > 0`, `β = onsBeta G D α`, every `n` and every `T ≥ 2`:
`(n/(2β)) log(TG²β²D² + 1) ≤ (n/(2β)) log T`.

**Formalization Note.** The printed step is false at `T = 1`: its left side is
`(n/(2β)) log(G²β²D² + 1) > 0 = (n/(2β)) log 1` for every `n ≥ 1`. It is stated for `T ≥ 2`. -/
theorem ons_log_step {n : ℕ} {G D α : ℝ} (hG : 0 < G) (hD : 0 < D) (hα : 0 < α) :
    ∀ T : ℕ, 2 ≤ T →
      n / (2 * onsBeta G D α) * Real.log (T * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 + 1)
        ≤ n / (2 * onsBeta G D α) * Real.log T := by sorry

end LogRegretOCO.ONS
