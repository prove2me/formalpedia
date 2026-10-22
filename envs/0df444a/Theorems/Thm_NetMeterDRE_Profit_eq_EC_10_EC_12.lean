-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_eq_EC_10_EC_12
-- name    : NetMeterDRE.Profit.eq_EC_10_EC_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:22.626326+00:00
-- url     : https://prove2.me/theorems/26b00007-bc8b-4bfd-af20-189b9de09343
-- title:
--   (EC.10) and (EC.12), p. ec4 (PDF 36) — closed forms of Πj(r) and Πj(0) in the supply function equilibrium
-- statement:
--   Consider the model of the paper under its standing assumptions, with region $j$ independent of the rest of the market, and let the wholesale price be $p^*_w(\mathcal D_w)$, a market-clearing price of the symmetric supply function equilibrium. Write $\widehat D_j = \beta D_j$, $\alpha = 2c(N-1)/((N-2)N)$, and $\nu$, $\widehat\nu$ as in (EC.8), (EC.13). Then utility $j$'s expected profit (6) under the retail-based rule is
--   $$\Pi_j(r) = \mathbb E\big[(\widehat D_j - \Delta_j)\,p_{u,j}\big] + \mathbb E\Big[(\Delta_j + K_j - \widehat D_j)\,\alpha\big(\widehat D_j - K_j - \Delta_j + \nu\big)\Big] - K_j\tilde c ,$$
--   and its expected profit with no DRE is
--   $$\Pi_j(0) = \mathbb E\Big[\widehat D_j\,p_{u,j} - (\widehat D_j - K_j)\,\alpha\big(\widehat D_j - K_j + \widehat\nu\big)\Big] - K_j\tilde c .$$
--
--   These closed forms reduce the comparison of $\Pi_j(r)$ and $\Pi_j(0)$ to an explicit expression in $K_j$, on which Lemma EC.1, Corollary 1 and Theorem 1 rest.
--
--   **Formalization Note** The independence of $(D_j,\Delta_j)$ from $((D_i,\Delta_i)_{i\ne j},\xi)$ is added: the paper uses it to replace the rest of the market by its mean $\nu$ (or $\widehat\nu$) but states only that the regions' generations are independent and that $\xi$ is independent of $\Delta_i$.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. ec4 (PDF 36), (EC.10) and (EC.12)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

theorem eq_EC_10_EC_12 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x)) :
    expProfit P U pw .r j D Δ ξ =
        ∫ ω, (U.beta * D j ω - Δ j ω) * U.pu j ∂P
        + ∫ ω, (Δ j ω + U.K j - U.beta * D j ω)
            * (alpha N c * (U.beta * D j ω - U.K j - Δ j ω + nu P U j D Δ ξ)) ∂P
        - U.K j * U.ct ∧
    noDREProfit P U pw j D ξ =
        ∫ ω, (U.beta * D j ω * U.pu j
            - (U.beta * D j ω - U.K j)
              * (alpha N c * (U.beta * D j ω - U.K j + nuHat P U j D ξ))) ∂P
        - U.K j * U.ct := by sorry

end NetMeterDRE.Profit
