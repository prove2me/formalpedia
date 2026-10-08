-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_profit_max_characterization
-- name    : MechanismDesign.PublicGoods.profit_max_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T00:20:48.779716+00:00
-- url     : https://prove2.me/theorems/a84574b1-2d84-49fd-807d-0210f74821c0
-- title:
--   Proposition 3.9 — characterization of the profit-maximizing public goods mechanism
-- statement:
--   Consider the public goods model of Börgers §3.3 and suppose every $F_i$ is regular. The designer's expected profit from a direct mechanism is revenue minus cost, $\int_\Theta \big(\sum_i t_i(\theta) - c\,q(\theta)\big) f(\theta)\,d\theta$.
--
--   **Proposition 3.9.** A direct mechanism $(q, t_1,\dots,t_N)$ is incentive-compatible and individually rational and maximizes expected profit among all such mechanisms if and only if for all $i\in I$ and all $\theta\in\Theta$:
--
--   1. $$q(\theta) = \begin{cases} 1 & \text{if } \sum_{i\in I}\theta_i > c + \sum_{i\in I}\dfrac{1-F_i(\theta_i)}{f_i(\theta_i)},\\ 0 & \text{otherwise;}\end{cases}$$
--   2. $T_i(\theta_i) = \theta_i Q_i(\theta_i) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx$.
--
--   Compared with Proposition 3.8, a profit-maximizing supplier of the public good produces less often than the welfare-maximizing designer.
--
--   **Formalization Note** Sufficiency is stated as printed, with condition 1 for every $\theta\in\Theta$; necessity yields condition 1 for almost every $\theta$ and condition 2 for every type, since changing $q$ on a null set is harmless. Mechanisms range over the class `IsDirect`.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.57–58, Proposition 3.9

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.9 (pp.57–58), profit maximization. Suppose every `F_i` is regular.
A direct mechanism is incentive-compatible, individually rational and maximizes expected profit
among all such mechanisms if and only if (i) `q(θ) = 1` iff
`∑ θ_i > c + ∑ (1 − F_i(θ_i))/f_i(θ_i)`, and (ii) `T_i(θ_i) = θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i`.
Sufficiency is stated with (i) for every `θ ∈ Θ`, as printed; necessity yields (i) for almost
every `θ` (the page's "for all `θ`" is false: `q` may be changed on a null set). -/
theorem profit_max_characterization {N : ℕ} (S : Setting N) (hreg : ∀ i, S.IsRegular i) :
    (∀ M : DirectMechanism N, M.IsDirect S →
        (∀ θ ∈ S.typeSpace, M.q θ = S.profitRule θ) →
        (∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, M.interimT S i x = x * M.interimQ S i x - ∫ y in S.θlo..x, M.interimQ S i y) →
        M.IsProfitMax S) ∧
    (∀ M : DirectMechanism N, M.IsProfitMax S →
        (∀ᵐ θ ∂S.μ, M.q θ = S.profitRule θ) ∧
        (∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, M.interimT S i x = x * M.interimQ S i x - ∫ y in S.θlo..x, M.interimQ S i y)) := by sorry

end MechanismDesign.PublicGoods
