-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_eq_EC_11
-- name    : NetMeterDRE.Profit.eq_EC_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:18.794239+00:00
-- url     : https://prove2.me/theorems/c551c8c1-4a45-46e7-975f-242c83c6db9f
-- title:
--   (EC.11), p. ec4 (PDF 36) — closed form of Πj(m) in the supply function equilibrium
-- statement:
--   Under the same hypotheses as (EC.10), utility $j$'s expected profit (6) under the market-based rule is
--   $$\Pi_j(m) = p_{u,j}\,\mathbb E\big[D^{\mathrm{reg}}_j + (D_j - \Delta_j)^+\big] + \mathbb E\Big[\big((\Delta_j + K_j - \widehat D_j) - (\Delta_j - D_j)^+\big)\,\alpha\big(\widehat D_j - K_j - \Delta_j + \nu\big)\Big] - K_j\tilde c ,$$
--   where $D^{\mathrm{reg}}_j = \widehat D_j - D_j$, $\widehat D_j = \beta D_j$, $\alpha = 2c(N-1)/((N-2)N)$ and $\nu$ is as in (EC.8).
--
--   This is the market-based counterpart of (EC.10): the buy-back of the customers' surplus is now paid at the wholesale price.
--
--   **Formalization Note** As in (EC.10), the independence of region $j$ from the rest of the market is an added hypothesis.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. ec4 (PDF 36), (EC.11)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

theorem eq_EC_11 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x)) :
    expProfit P U pw .m j D Δ ξ =
        U.pu j * ∫ ω, (U.beta * D j ω - D j ω + max (D j ω - Δ j ω) 0) ∂P
        + ∫ ω, ((Δ j ω + U.K j - U.beta * D j ω) - max (Δ j ω - D j ω) 0)
            * (alpha N c * (U.beta * D j ω - U.K j - Δ j ω + nu P U j D Δ ξ)) ∂P
        - U.K j * U.ct := by sorry

end NetMeterDRE.Profit
