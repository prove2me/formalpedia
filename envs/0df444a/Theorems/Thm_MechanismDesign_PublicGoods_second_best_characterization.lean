-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_second_best_characterization
-- name    : MechanismDesign.PublicGoods.second_best_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T00:20:32.525368+00:00
-- url     : https://prove2.me/theorems/bb1a409f-5618-498b-9354-9c8cc834391e
-- title:
--   Proposition 3.8 — characterization of the second best public goods mechanism
-- statement:
--   Consider the public goods model of Börgers §3.3 with $N\underline\theta < c < N\bar\theta$, and suppose every $F_i$ is regular: $\psi_i(\theta_i) = \theta_i - (1-F_i(\theta_i))/f_i(\theta_i)$ is strictly increasing. A direct mechanism is **second best** if it is incentive-compatible, individually rational and ex ante budget balanced, and maximizes expected welfare $\int_\Theta \big((\sum_i\theta_i) q(\theta) - \sum_i t_i(\theta)\big) f(\theta)\,d\theta$ among all such mechanisms.
--
--   **Proposition 3.8.** A direct mechanism $(q, t_1, \dots, t_N)$ is second best if and only if:
--
--   1. there is some $\lambda > 0$ such that for all $\theta\in\Theta$
--   $$q(\theta) = \begin{cases} 1 & \text{if } \sum_{i\in I}\theta_i > c + \sum_{i\in I}\dfrac{\lambda}{1+\lambda}\dfrac{1-F_i(\theta_i)}{f_i(\theta_i)},\\ 0 & \text{otherwise;}\end{cases}$$
--   2. $\displaystyle\int_\Theta q(\theta)\Big[\sum_{i\in I}\Big(\theta_i - \frac{1-F_i(\theta_i)}{f_i(\theta_i)}\Big) - c\Big] f(\theta)\,d\theta = 0$;
--   3. for all $i\in I$ and $\theta_i \in [\underline\theta,\bar\theta]$: $T_i(\theta_i) = \theta_i Q_i(\theta_i) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx$.
--
--   The second best mechanism undersupplies the public good: it produces only when the sum of valuations exceeds a bound strictly larger than $c$.
--
--   **Formalization Note** The statement is split into its two directions. Sufficiency is stated as printed, with condition 1 for every $\theta\in\Theta$. Necessity yields condition 1 for almost every $\theta$ (with respect to the type distribution) together with conditions 2 and 3: the printed "for all $\theta$" is false in the necessity direction, because changing $q$ on a null set of type vectors changes neither incentives nor welfare. All mechanisms range over the class `IsDirect` (measurability and integrability made explicit).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.56–57, Proposition 3.8 (Assumption 3.2)

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.8 (pp.56–57), second best. Suppose `N θ̲ < c < N θ̄` and every `F_i`
is regular. A direct mechanism is incentive-compatible, individually rational, ex ante budget
balanced and maximizes expected welfare among all such mechanisms if and only if
(i) for some `λ > 0`, `q(θ) = 1` iff `∑ θ_i > c + ∑ (λ/(1+λ)) (1 − F_i(θ_i))/f_i(θ_i)`;
(ii) `∫_Θ q(θ) (∑_i ψ_i(θ_i) − c) f(θ) dθ = 0`; (iii) `T_i(θ_i) = θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i`.
Sufficiency is stated with (i) for every `θ ∈ Θ`, as printed; necessity yields (i) for almost
every `θ` (the page's "for all `θ`" is false: `q` may be changed on a null set). -/
theorem second_best_characterization {N : ℕ} (S : Setting N)
    (hlow : (N : ℝ) * S.θlo < S.c) (hhigh : S.c < (N : ℝ) * S.θhi)
    (hreg : ∀ i, S.IsRegular i) :
    (∀ M : DirectMechanism N, M.IsDirect S →
        (∃ lam : ℝ, 0 < lam ∧ ∀ θ ∈ S.typeSpace, M.q θ = S.secondBestRule lam θ) →
        ∫ θ, M.q θ * (∑ i, S.virtualValuation i (θ i) - S.c) ∂S.μ = 0 →
        (∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, M.interimT S i x = x * M.interimQ S i x - ∫ y in S.θlo..x, M.interimQ S i y) →
        M.IsSecondBest S) ∧
    (∀ M : DirectMechanism N, M.IsSecondBest S →
        (∃ lam : ℝ, 0 < lam ∧ ∀ᵐ θ ∂S.μ, M.q θ = S.secondBestRule lam θ) ∧
        ∫ θ, M.q θ * (∑ i, S.virtualValuation i (θ i) - S.c) ∂S.μ = 0 ∧
        (∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, M.interimT S i x = x * M.interimQ S i x - ∫ y in S.θlo..x, M.interimQ S i y)) := by sorry

end MechanismDesign.PublicGoods
