-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_uniform_profit_threshold
-- name    : MechanismDesign.BilateralTrade.uniform_profit_threshold
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-03T00:55:43.567516+00:00
-- url     : https://prove2.me/theorems/defc624e-22e7-43ae-b533-d599175c6755
-- title:
--   Proposition 3.16 -- uniform values: the profit maximizer trades iff $\theta_B - \theta_S > 1/2$
-- statement:
--   Suppose $\theta_S$ and $\theta_B$ are independent and uniformly distributed on $[0,1]$ (Example 3.4). Consider the class of incentive-compatible and individually rational direct mechanisms, and the designer's expected profit $\mathbb E[t_B(\theta) - t_S(\theta)]$. A profit-maximizing mechanism exists in this class, and a mechanism of the class maximizes expected profit in it if and only if its trading rule satisfies, for almost every $\theta$,
--
--   $$
--   q(\theta) = 1 \iff \theta_B - \theta_S > \tfrac12 .
--   $$
--
--   Compared with Proposition 3.15, the profit-maximizing designer arranges less trade than the welfare-maximizing one.
--
--   **Formalization Note** The book's definite article is rendered as existence plus a characterization; "trade takes place iff" is stated almost surely. Mechanisms are measurable with integrable transfers.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.74, Proposition 3.16, Eq. (3.82) (Example 3.4, p.73)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.16 (Example 3.4, p.74): with both values uniform on `[0, 1]`, an expected
profit-maximizing mechanism exists among the well-defined, incentive-compatible and individually
rational direct mechanisms, and a mechanism of that class maximizes expected profit `E[t_B − t_S]`
in it if and only if, almost surely, trade takes place exactly when `θ_B − θ_S > 1/2`. -/
theorem uniform_profit_threshold :
    (∃ m : DirectMechanism uniformEnv, m.Admissible ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible →
        m'.expectedSurplus ≤ m.expectedSurplus) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible →
          m'.expectedSurplus ≤ m.expectedSurplus) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 2 < θ.2 - θ.1 then 1 else 0) := by sorry

end MechanismDesign.BilateralTrade
