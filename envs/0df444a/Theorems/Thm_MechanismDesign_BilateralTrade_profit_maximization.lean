-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_profit_maximization
-- name    : MechanismDesign.BilateralTrade.profit_maximization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:55:43.723952+00:00
-- url     : https://prove2.me/theorems/fec83601-2b57-4bef-84f9-941577c57fb6
-- title:
--   Proposition 3.14 -- the profit-maximizing trading mechanism
-- statement:
--   In the bilateral trade environment, suppose $F_S$ and $F_B$ are regular, i.e. $\psi_S(\theta_S) = \theta_S + F_S(\theta_S)/f_S(\theta_S)$ and $\psi_B(\theta_B) = \theta_B - (1-F_B(\theta_B))/f_B(\theta_B)$ are increasing. The designer's expected profit is $\mathbb E[t_B(\theta) - t_S(\theta)]$. For an incentive-compatible and individually rational direct mechanism, the following conditions are necessary and sufficient for it to maximize expected profit among all such mechanisms:
--
--   1. $$
--   q(\theta) = \begin{cases} 1 & \text{if } \theta_B - \frac{1-F_B(\theta_B)}{f_B(\theta_B)} > \theta_S + \frac{F_S(\theta_S)}{f_S(\theta_S)},\\ 0 & \text{otherwise;}\end{cases}
--   $$
--   2. for all $\theta_B \in [\underline\theta_B, \overline\theta_B]$ and $\theta_S \in [\underline\theta_S, \overline\theta_S]$,
--   $$
--   T_B(\theta_B) = \theta_B Q_B(\theta_B) - \int_{\underline\theta_B}^{\theta_B} Q_B(x)\,dx, \qquad T_S(\theta_S) = \overline\theta_S - (1 - Q_S(\theta_S))\theta_S - \int_{\theta_S}^{\overline\theta_S} (1 - Q_S(x))\,dx .
--   $$
--
--   A profit-maximizing platform facilitates less trade than a welfare-maximizing designer.
--
--   **Formalization Note** Sufficiency assumes (1) for every $\theta \in \Theta$ together with (2). Necessity concludes (2) as printed and (1) only for almost every $\theta$ with $\psi_B(\theta_B) \ne \psi_S(\theta_S)$. Two corrections of the page are involved: changing $q$ on a null set changes nothing, and because regularity is only weak monotonicity, the tie set $\{\psi_B(\theta_B) = \psi_S(\theta_S)\}$ can have positive probability, and there the value of $q$ does not affect profit. Mechanisms are measurable with integrable transfers (Ch. 2 note 2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.72, Proposition 3.14 (with Assumption 3.3, p.70)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.14 (p.72), profit maximization. Assume `F_S`, `F_B` are regular, and let `m` be
a well-defined, incentive-compatible and individually rational direct mechanism. Sufficiency: if
(i) `q(θ) = 1` iff `ψ_B(θ_B) > ψ_S(θ_S)` for every `θ ∈ Θ` and (ii) the interim payments are
the incentive-compatible ones with binding participation of `θ̄_S` and `θ̲_B`, then `m`
maximizes the expected profit `E[t_B − t_S]` among all such mechanisms. Necessity: a maximizer
satisfies (ii), and (i) almost everywhere off the tie set `ψ_B(θ_B) = ψ_S(θ_S)` (under weak
regularity that set may have positive probability and the profit does not depend on `q` there). -/
theorem profit_maximization (E : Environment) (hreg : E.Regular) (m : DirectMechanism E)
    (hm : m.Admissible) :
    ((∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) →
      (∀ᵐ θ ∂E.prior, E.psiB θ.2 ≠ E.psiS θ.1 → m.q θ = profitRule E θ) ∧
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) ∧
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z))) ∧
    ((∀ θ ∈ E.typeSpace, m.q θ = profitRule E θ) →
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) →
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z)) →
      ∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) := by sorry

end MechanismDesign.BilateralTrade
