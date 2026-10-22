-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_corollary_1
-- name    : NetMeterDRE.Profit.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:28.855984+00:00
-- url     : https://prove2.me/theorems/13172f5c-dc7a-42e7-8bc4-587445705b06
-- title:
--   Corollary 1 = Lemma EC.3, p. 13 (PDF 13), p. ec6 (PDF 38) — ∂(Πj(ℓ) − Πj(0))/∂Kj < 0, with the printed slope
-- statement:
--   Consider the model of the paper under its standing assumptions, with region $j$ independent of the rest of the market and the wholesale price a market-clearing price of the symmetric supply function equilibrium. Let $\ell \in \{r,m\}$ and $\alpha = 2c(N-1)/((N-2)N)$. Vary utility $j$'s existing resources $K_j$, keeping every other datum fixed. Suppose that $\mathbb E[\Delta_j] > 0$ or $\nu < \widehat\nu$. Then $K_j \mapsto \Pi_j(\ell) - \Pi_j(0)$ is differentiable at every $K_j$, with
--   $$\frac{\partial(\Pi_j(r) - \Pi_j(0))}{\partial K_j} = \mathbb E\big[-2\alpha\Delta_j + \alpha(\nu - \widehat\nu)\big],$$
--   $$\frac{\partial(\Pi_j(m) - \Pi_j(0))}{\partial K_j} = \mathbb E\big[-\alpha\Delta_j + \alpha(\nu - \widehat\nu)\big] + \alpha\,\mathbb E\big[-\Delta_j + (\Delta_j - D_j)^+\big],$$
--   and both derivatives are strictly negative.
--
--   This is Corollary 1 of the paper, proved as Lemma EC.3: a more market-reliant utility (smaller $K_j$) gains more from net-metered DRE. Together with Lemma EC.1 it yields the threshold $\bar K_\ell$ of Theorem 1.
--
--   **Formalization Note** The hypothesis "$\mathbb E[\Delta_j] > 0$ or $\nu < \widehat\nu$" is added. The paper argues from $\widehat\nu > \nu$, which holds only when some other region has generation; without the added hypothesis ($\Delta \equiv 0$ everywhere) the derivative is $0$. The derivative is stated at every real $K_j$ (the paper's proof says "suppose that $K_j > 0$"); the expression is affine in $K_j$, so this is a stronger form. The independence of region $j$ is added as in (EC.10).
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. 13 (PDF 13), Corollary 1; p. ec6 (PDF 38), Lemma EC.3 and its proof

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

theorem corollary_1 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x))
    (ℓ : Rule) (hpos : 0 < ∫ ω, Δ j ω ∂P ∨ nu P U j D Δ ξ < nuHat P U j D ξ) :
    let α := alpha N c
    let slope : ℝ :=
      match ℓ with
      | .r => ∫ ω, (-2 * α * Δ j ω + α * (nu P U j D Δ ξ - nuHat P U j D ξ)) ∂P
      | .m => ∫ ω, (-α * Δ j ω + α * (nu P U j D Δ ξ - nuHat P U j D ξ)) ∂P
              + α * ∫ ω, (-Δ j ω + max (Δ j ω - D j ω) 0) ∂P
    (∀ k : ℝ, HasDerivAt
        (fun Kj : ℝ => expProfit P (U.setK j Kj) pw ℓ j D Δ ξ
                        - noDREProfit P (U.setK j Kj) pw j D ξ) slope k) ∧
      slope < 0 := by sorry

end NetMeterDRE.Profit
