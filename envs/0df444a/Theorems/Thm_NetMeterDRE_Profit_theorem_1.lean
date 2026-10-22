-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_theorem_1
-- name    : NetMeterDRE.Profit.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:21.768831+00:00
-- url     : https://prove2.me/theorems/11d9a4c6-e475-4741-945a-642ba97f3ef6
-- title:
--   Theorem 1, p. 12 (PDF 12) — net-metered DRE strictly raises utility j's expected profit iff Kj < K̄ℓ and γℓ < p∗w′(Dw)
-- statement:
--   Consider the model of Sunar and Swaminathan: $N > 2$ generators with costs $cq^2$ play the symmetric supply function equilibrium, so the wholesale price $p^*_w(\mathcal D_w)$ is the market-clearing price of the profile $S(p) = (N-2)p/((N-1)2c)$; utilities $i$ have random demands $D_i$, $\widehat D_i = \beta D_i$, random distributed generation $\Delta_i$, existing resources $K_i \ge 0$ at unit cost $\tilde c$, and retail prices $p_{u,i} > \tilde c$; and the net wholesale demand is $\mathcal D_w = \sum_i(\widehat D_i - K_i - \Delta_i) + \xi$. Assume region $j$ is independent of the rest of the market. Fix a net metering rule $\ell \in \{r, m\}$ and let $\gamma_\ell$ be the constant (EC.16) (for $\ell = r$) or (EC.17) (for $\ell = m$); it does not depend on $K_j$.
--
--   **Theorem.** There is a threshold $\bar K_\ell$ such that for every level $K_j \ge 0$ of utility $j$'s existing resources (all other data fixed),
--   $$\Pi_j(\ell) > \Pi_j(0) \iff K_j < \bar K_\ell \ \text{ and } \ \gamma_\ell < p^{*\prime}_w(\mathcal D_w).$$
--   That is, net-metered distributed renewable energy strictly raises utility $j$'s expected profit, compared with the case of no such generation, exactly when the utility's existing resources are small and the wholesale price is sensitive enough to the net wholesale demand.
--
--   This is the paper's main result: it identifies when a utility should not lobby against net-metered DRE.
--
--   **Formalization Note** $\gamma_\ell$ is the explicit expression of (EC.16)/(EC.17), not an existential constant; $\bar K_\ell$ is existential, as printed, and is chosen before $K_j$, so it may depend on every datum except $K_j$. $\Pi_j(\ell)$ and $\Pi_j(0)$ are both evaluated in the market with utility $j$'s resources set to $K_j$. The derivative $p^{*\prime}_w(\mathcal D_w)$ is taken at an arbitrary point (it is constant). Added: the independence of $(D_j,\Delta_j)$ from the rest of the market and $\xi$, which the proof uses. Dropped, making the statement stronger: condition (4)(b) and condition (7), which the proof does not use and which depend on $K_j$, and the differentiability of the distribution functions; laws are only required to be bounded with supports as in §2.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), pp. 12–13 (PDF 12–13), Theorem 1; proof on p. ec6 (PDF 38)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

theorem theorem_1 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x))
    (ℓ : Rule) (x₀ : ℝ) :
    ∃ Kbar : ℝ, ∀ Kj : ℝ, 0 ≤ Kj →
      (noDREProfit P (U.setK j Kj) pw j D ξ < expProfit P (U.setK j Kj) pw ℓ j D Δ ξ ↔
        Kj < Kbar ∧ gamma P U ℓ j D Δ ξ < deriv pw x₀) := by sorry

end NetMeterDRE.Profit
