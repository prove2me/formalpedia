-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_lemma_EC_1
-- name    : NetMeterDRE.Profit.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:25.38297+00:00
-- url     : https://prove2.me/theorems/4f164c84-05f6-45c6-b6b1-fa280390e828
-- title:
--   Lemma EC.1 (= Corollary 2), pp. ec4–ec5 (PDF 36–37) — when Kj = 0, DRE strictly raises Πj iff γℓ < p∗w′(Dw)
-- statement:
--   Consider the model of the paper under its standing assumptions, with region $j$ independent of the rest of the market and the wholesale price $p^*_w$ a market-clearing price of the symmetric supply function equilibrium. Suppose utility $j$ has no existing resources, $K_j = 0$, and let $\ell \in \{r, m\}$. Suppose further that the denominator of $\gamma_\ell$ in (EC.16)/(EC.17) is strictly positive. Then net-metered DRE under the rule $\ell$ strictly raises utility $j$'s expected profit if and only if $\gamma_\ell$ is below the slope of the wholesale price:
--   $$\Pi_j(\ell) > \Pi_j(0) \iff \gamma_\ell < p^{*\prime}_w(\mathcal D_w).$$
--
--   This is Lemma EC.1, which the paper also states as Corollary 2 for a market-reliant utility ($K_j = 0$). It gives the value of Theorem 1's threshold condition at $K_j = 0$.
--
--   **Formalization Note** The positivity of $\gamma_\ell$'s denominator is added. Without it the statement is false: with one utility, $N = 3$, $c = 1$, $\beta = 2$, $p_{u,j} = 20$, $\tilde c = 1/10$, $K_j = 0$, $\xi \equiv 1$ and $(D_j,\Delta_j)$ equal to $(0,10)$ or $(10,0)$ with probability $1/2$ each, the denominator of $\gamma_r$ is $-45$, so $\gamma_r = -20/9 < \alpha = 4/3$, but $\Pi_j(r) - \Pi_j(0) = -160$. The derivative $p^{*\prime}_w(\mathcal D_w)$ is taken at an arbitrary point; it equals $\alpha$ everywhere. The independence of region $j$ is added as in (EC.10).
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. ec4 (PDF 36), Lemma EC.1; p. ec5 (PDF 37), (EC.16), (EC.17) and proof; p. 14 (PDF 14), Corollary 2

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

theorem lemma_EC_1 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x))
    (ℓ : Rule) (hK : U.K j = 0) (hden : 0 < gammaDen P U ℓ j D Δ ξ) (x₀ : ℝ) :
    noDREProfit P U pw j D ξ < expProfit P U pw ℓ j D Δ ξ ↔
      gamma P U ℓ j D Δ ξ < deriv pw x₀ := by sorry

end NetMeterDRE.Profit
