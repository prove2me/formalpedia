-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_second_best
-- name    : MechanismDesign.BilateralTrade.second_best
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:55:16.536087+00:00
-- url     : https://prove2.me/theorems/46987148-44ff-4de0-aa03-ae0bb177640e
-- title:
--   Proposition 3.13 -- the second-best trading mechanism
-- statement:
--   In the bilateral trade environment, suppose $\underline\theta_B < \overline\theta_S$ and $\overline\theta_B > \underline\theta_S$, and that $F_S$ and $F_B$ are regular: $\psi_S(\theta_S) = \theta_S + F_S(\theta_S)/f_S(\theta_S)$ and $\psi_B(\theta_B) = \theta_B - (1-F_B(\theta_B))/f_B(\theta_B)$ are increasing. A direct mechanism $(q, t_S, t_B)$ is incentive-compatible, individually rational and ex ante budget balanced, and maximizes expected welfare among all such mechanisms, if and only if:
--
--   1. there is some $\lambda > 0$ such that for all $\theta \in \Theta$
--   $$
--   q(\theta) = \begin{cases} 1 & \text{if } \theta_B - \frac{\lambda}{1+\lambda}\frac{1-F_B(\theta_B)}{f_B(\theta_B)} \ge \theta_S + \frac{\lambda}{1+\lambda}\frac{F_S(\theta_S)}{f_S(\theta_S)},\\ 0 & \text{otherwise;}\end{cases}
--   $$
--   2. exact budget balance holds:
--   $$
--   \int_\Theta q(\theta)\big[\psi_B(\theta_B) - \psi_S(\theta_S)\big] f(\theta)\,d\theta = \overline\theta_S - \int_\Theta \psi_S(\theta_S) f(\theta)\,d\theta ;
--   $$
--   3. for all $\theta_B \in [\underline\theta_B, \overline\theta_B]$ and $\theta_S \in [\underline\theta_S, \overline\theta_S]$,
--   $$
--   T_B(\theta_B) = \theta_B Q_B(\theta_B) - \int_{\underline\theta_B}^{\theta_B} Q_B(x)\,dx, \qquad T_S(\theta_S) = \overline\theta_S - (1 - Q_S(\theta_S))\theta_S - \int_{\theta_S}^{\overline\theta_S} (1 - Q_S(x))\,dx .
--   $$
--
--   In the second-best mechanism trade happens less often than efficiency requires: the buyer's value minus a discount must exceed the seller's value plus an increment.
--
--   **Formalization Note** The statement is split into its two directions. Sufficiency assumes (1) on all of $\Theta$ (and that the mechanism is well defined). Necessity concludes (1) only for almost every $\theta$: changing $q$ on a null set leaves every constraint and the objective unchanged, so the page's "for all $\theta \in \Theta$" cannot be necessary; (2) and (3) are concluded as printed. Welfare is the expectation of Eq. (3.60), $\theta_S + q(\theta)(\theta_B-\theta_S) + t_S - t_B$. Mechanisms are measurable with integrable transfers (Ch. 2 note 2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.71, Proposition 3.13 (with Assumption 3.3, p.70)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.13 (p.71), second best. Assume `θ̲_B < θ̄_S`, `θ̄_B > θ̲_S` and that `F_S`,
`F_B` are regular. A direct mechanism is well-defined, incentive-compatible, individually rational,
ex ante budget balanced and maximizes expected welfare among all such mechanisms if and only if
(i) its trading rule is the rule (3.70) for some `λ > 0`, (ii) exact budget balance holds, and
(iii) the interim payments are the incentive-compatible ones with binding participation of
`θ̄_S` and `θ̲_B`. Necessity of (i) is stated almost everywhere (the page's "for all `θ ∈ Θ`" is
false on null sets); sufficiency assumes (i) on all of `Θ`. -/
theorem second_best (E : Environment) (hB : E.loB < E.hiS) (hS : E.loS < E.hiB)
    (hreg : E.Regular) (m : DirectMechanism E) :
    ((m.Admissible ∧ m.ExAnteBB ∧
        ∀ m' : DirectMechanism E, m'.Admissible → m'.ExAnteBB → m'.welfare ≤ m.welfare) →
      (∃ lam : ℝ, 0 < lam ∧ ∀ᵐ θ ∂E.prior, m.q θ = lambdaRule E lam θ) ∧
      (∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior = E.hiS - ∫ θ, E.psiS θ.1 ∂E.prior) ∧
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) ∧
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z))) ∧
    (m.WellDefined →
      (∃ lam : ℝ, 0 < lam ∧ ∀ θ ∈ E.typeSpace, m.q θ = lambdaRule E lam θ) →
      (∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior = E.hiS - ∫ θ, E.psiS θ.1 ∂E.prior) →
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) →
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z)) →
      m.Admissible ∧ m.ExAnteBB ∧
        ∀ m' : DirectMechanism E, m'.Admissible → m'.ExAnteBB → m'.welfare ≤ m.welfare) := by sorry

end MechanismDesign.BilateralTrade
