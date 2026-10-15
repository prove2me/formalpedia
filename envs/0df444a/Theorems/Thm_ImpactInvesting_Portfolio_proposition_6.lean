-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_proposition_6
-- name    : ImpactInvesting.Portfolio.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:38.049767+00:00
-- url     : https://prove2.me/theorems/61f7c795-8e2d-4649-bc12-a2474c964d4c
-- title:
--   Proposition 6, p. 21 — mean (30) and variance (31) of an impact portfolio's excess return under (A1); (31) corrected
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, and let $\sigma_\alpha > 0$, $-1 < \rho < 1$. Let $\mathcal S \subseteq \{1, \dots, N\}$ be a set of ranks by the impact factor $X$ and let $\{\omega_i : i \in \mathcal S\}$ be portfolio weights with $\sum_{i\in\mathcal S}\omega_i = 1$. The excess return of the impact portfolio holding the security of rank $i$ with weight $\omega_i$ is
--   $$\tilde\alpha = \sum_{i\in\mathcal S}\omega_i\,\alpha_{[i:N]}.$$
--   Write $\mu_i = \mathbb E[\alpha_{[i:N]}]$, $\sigma_i^2 = \operatorname{Var}(\alpha_{[i:N]})$ and $\sigma_{ij} = \operatorname{Cov}(\alpha_{[i:N]}, \alpha_{[j:N]})$. Then
--   $$\mathbb E[\tilde\alpha] = \sum_{i\in\mathcal S}\omega_i\mu_i = \rho\,\sigma_\alpha\sum_{i\in\mathcal S}\omega_i\,\mathbb E[X_{i:N}],$$
--   and
--   $$\operatorname{Var}(\tilde\alpha) = \sum_{i\in\mathcal S}\omega_i^2\sigma_i^2 + 2\sum_{i<j \in\mathcal S}\omega_i\omega_j\sigma_{ij} = \sigma_\alpha^2\Big((1-\rho^2)\sum_{i\in\mathcal S}\omega_i^2 + \rho^2\Big(\sum_{i\in\mathcal S}\omega_i^2\operatorname{Var}(X_{i:N}) + 2\sum_{i<j\in\mathcal S}\omega_i\omega_j\operatorname{Cov}(X_{i:N}, X_{j:N})\Big)\Big).$$
--
--   In particular the sign of $\rho$ determines the sign of the expected excess return of a portfolio of top-ranked securities: this is the paper's quantification of whether impact investing helps or hurts.
--
--   **Correction.** The paper prints the second line of (31) with $1 - \rho^2$ in place of $(1-\rho^2)\sum_{i\in\mathcal S}\omega_i^2$. The two agree only when $\sum_{i\in\mathcal S}\omega_i^2 = 1$ or $\rho^2 = 1$; for $\rho = 0$, $\mathcal S = \{1, 2\}$, $\omega = (\tfrac12, \tfrac12)$ the true variance is $\sigma_\alpha^2/2$ while the printed formula gives $\sigma_\alpha^2$. The corrected form stated here is what the first line of (31) and Proposition 2 give.
--
--   **Formalization Note.** Ranks are 0-based (`i : Fin N` is rank $i+1$); $\mathcal S$ is a `Finset (Fin N)` of ranks and the weights are a function `w : Fin N → ℝ` read on $\mathcal S$. The sum $\sum_{i<j\in\mathcal S}$ is `∑ i ∈ S, ∑ j ∈ S with i < j` in the order of `Fin N` (any order gives the same value since the summand is symmetric). The hypothesis $\sum_{i\in\mathcal S}\omega_i = 1$ is the page's and is kept, although the identities do not use it.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 21, §5.1, (28)–(29) and Proposition 6, (30)–(31)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem proposition_6 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1)
    (S : Finset (Fin N)) (w : Fin N → ℝ) (hw : ∑ i ∈ S, w i = 1) :
    P[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω] =
        ∑ i ∈ S, w i * P[inducedOrderStatRV X α i] ∧
    P[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω] =
        ρ * σα * ∑ i ∈ S, w i * P[orderStatRV X i] ∧
    Var[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω; P] =
        ∑ i ∈ S, w i ^ 2 * Var[inducedOrderStatRV X α i; P] +
          2 * ∑ i ∈ S, ∑ j ∈ S with i < j,
            w i * w j * cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] ∧
    Var[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω; P] =
        σα ^ 2 * ((1 - ρ ^ 2) * ∑ i ∈ S, w i ^ 2 +
          ρ ^ 2 * (∑ i ∈ S, w i ^ 2 * Var[orderStatRV X i; P] +
            2 * ∑ i ∈ S, ∑ j ∈ S with i < j,
              w i * w j * cov[orderStatRV X i, orderStatRV X j; P])) := by sorry

end ImpactInvesting.Portfolio
