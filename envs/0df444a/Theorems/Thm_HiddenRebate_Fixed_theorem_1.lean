-- Prove2me | Theorems.Thm_HiddenRebate_Fixed_theorem_1
-- name    : HiddenRebate.Fixed.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:04.82797+00:00
-- url     : https://prove2.me/theorems/48665d63-d607-4ffe-a957-280973e1e06c
-- title:
--   Theorem 1, p. 12 — for r < r̄, picking S iff zS ≤ zW − r and paying F = r iff S wins is incentive-compatible and minimizes the retailer's expected cost
-- statement:
--   **Theorem 1 (Fan, Chen & Tang).** Let the manufacturers' prices $x_S, x_W$ be iid with a law $\mu$ that has a density on $[0,\infty)$ and a finite mean, let $r \ge 0$ be the hidden rebate, and let $\bar r$ be the threshold of footnote 15. Let $\langle A^*, F^*\rangle$ be the contract (15):
--   $$A^*(z) = \begin{cases} S & z_S \le z_W - r,\\ W & z_S > z_W - r,\end{cases}\qquad F^*(z) = \begin{cases} r & A^*(z) = S,\\ 0 & \text{otherwise.}\end{cases}$$
--   If $r < \bar r$, then
--
--   1. $\langle A^*, F^*\rangle$ is admissible and incentive compatible (13), so the intermediary reports $(z_S, z_W) = (q_S, q_W)$ truthfully;
--   2. its expected cost (14) is finite; and
--   3. it solves the retailer's problem (14): for every admissible deterministic contract $\langle A, F\rangle$ satisfying (13) with integrable cost,
--   $$E\,C(q; \langle A^*, F^*\rangle) \le E\,C(q; \langle A, F\rangle).$$
--
--   The theorem says that, for small rebates, the retailer cannot do better than to pay the intermediary a fee equal to the hidden rebate whenever the ethical manufacturer is chosen, and to handicap $W$'s quote by $r$.
--
--   **Formalization Note** Deterministic contracts are pairs of measurable maps $A : \mathbb R^2 \to \{S,W\}$, $F : \mathbb R^2 \to [0,\infty)$; the reduction from general to direct mechanisms (Strausz 2016's revelation principle) is not part of the statement. Added to the page: $E[x_S] < \infty$, $r \ge 0$, competitors with integrable cost (a non-integrable non-negative cost is $+\infty$ and cannot be optimal), and the guard $\bar G(T)\bar G(a) > 0$ in the first infimum of $\bar r$. Footnote 15 is stated as printed; its second term is not divided by $\bar G(T)$, which only makes $\bar r$ smaller (the hypothesis stronger). For iid Exp(1) costs, $\bar r = 1/2 - 1/e \approx 0.132 > 0$; for any bounded support $\bar r \le 0$ and the theorem is vacuous, as on the page.
-- source:
--   Fan, Chen & Tang, Mechanism design for managing hidden rebates and inflated quotes of a procurement service provider, SSRN preprint 3514358, p. 12, Theorem 1 and footnote 15

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

namespace HiddenRebate.Fixed

open MeasureTheory

/-- Theorem 1, p. 12: when `r < r̄` (footnote 15), the contract ⟨A∗, F∗⟩ of (15) induces truthful
reporting and solves the retailer's problem (14) among all deterministic contracts satisfying (13). -/
theorem theorem_1 (μ : Measure ℝ) (r : ℝ) (hμ : Standing μ r) (hr : r < rbar μ) :
    Feasible (contractStar r).1 (contractStar r).2 ∧
    IsIC r (contractStar r).1 (contractStar r).2 ∧
    Integrable (costIntegrand r (contractStar r).1 (contractStar r).2) (μ.prod μ) ∧
    ∀ (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ), Feasible A F → IsIC r A F →
      Integrable (costIntegrand r A F) (μ.prod μ) →
      cost μ r (contractStar r).1 (contractStar r).2 ≤ cost μ r A F := by sorry

end HiddenRebate.Fixed
