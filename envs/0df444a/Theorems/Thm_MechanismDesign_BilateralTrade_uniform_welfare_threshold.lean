-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_uniform_welfare_threshold
-- name    : MechanismDesign.BilateralTrade.uniform_welfare_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:55:52.893207+00:00
-- url     : https://prove2.me/theorems/bea58c30-7140-4fd3-82c2-5e71a8390be7
-- title:
--   Proposition 3.15 -- uniform values: the second best trades iff $\theta_B - \theta_S > 1/4$
-- statement:
--   Suppose $\theta_S$ and $\theta_B$ are independent and uniformly distributed on $[0,1]$ (Example 3.4). Consider the class of incentive-compatible, individually rational and ex post budget balanced direct mechanisms. A welfare-maximizing mechanism exists in this class, and a mechanism of the class maximizes expected welfare in it if and only if its trading rule satisfies, for almost every $\theta$,
--
--   $$
--   q(\theta) = 1 \iff \theta_B - \theta_S > \tfrac14 .
--   $$
--
--   The threshold $1/4$ is the second-best rule of Proposition 3.13 with $\lambda = 1/2$; it coincides with the trading region of the linear equilibrium of the Chatterjee–Samuelson split-the-difference double auction.
--
--   **Formalization Note** The book's definite article ("the welfare-maximizing … mechanism") is rendered as existence plus a characterization; "trade takes place iff" is stated almost surely, since the trading rule of an optimal mechanism is determined only up to null sets. Mechanisms are measurable with integrable transfers.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.74, Proposition 3.15, Eq. (3.81) (Example 3.4, p.73)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.15 (Example 3.4, p.74): with both values uniform on `[0, 1]`, a
welfare-maximizing mechanism exists among the well-defined, incentive-compatible, individually
rational and ex post budget balanced direct mechanisms, and a mechanism of that class maximizes
expected welfare in it if and only if, almost surely, trade takes place exactly when
`θ_B − θ_S > 1/4`. -/
theorem uniform_welfare_threshold :
    (∃ m : DirectMechanism uniformEnv, m.Admissible ∧ m.ExPostBB ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible → m'.ExPostBB → m'.welfare ≤ m.welfare) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible → m.ExPostBB →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible → m'.ExPostBB →
          m'.welfare ≤ m.welfare) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 4 < θ.2 - θ.1 then 1 else 0) := by sorry

end MechanismDesign.BilateralTrade
