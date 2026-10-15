-- Prove2me | Theorems.Thm_FreeSamples_Revenue_theorem_1b
-- name    : FreeSamples.Revenue.theorem_1b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:52.603428+00:00
-- url     : https://prove2.me/theorems/ce50297a-c798-427d-a220-ffe3ce173634
-- title:
--   Theorem 1(b), p. 18 — if the Seller-side drift of BR is non-positive for all states, one-round selling is optimal
-- statement:
--   Let $u$ satisfy HasMax and Assumption 1, and let $BR$ satisfy the growth hypothesis on variances in $(0,\sigma_0^2]$. Assume that the Seller-side drift is non-positive for every mean $x\in\mathbb R$, every misspecification $g\in\mathbb R$, and every positive variance $v$:
--   $$\tfrac12 BR_{\theta\theta}(x,v)-BR_{\sigma^2}(x,v)+\frac{g}{v}BR_\theta(x,v)\le 0.$$
--   Then, under the Seller's model, for every free-sample policy (bounded stopping time $T$ of the data filtration), the revenue $BR(\theta_T,\sigma_T^2)$ is integrable and
--   $$\mathbb E^S_0\big[BR(\theta_T,\sigma_T^2)\big]\le BR(\theta_0,\sigma_0^2).$$
--   So selling the whole dataset in one round is optimal among free-sample policies. This is the converse half of Theorem 1.
--
--   **Formalization Note.** The hypothesis follows the printed universal quantifiers in (5), with $\mathbb R_+$ read as positive variance because the formula divides by $v$. Since the expression is affine in $g$, this condition forces $BR_\theta=0$ on positive variances. The paper's application on p. 33 instead checks the realized $g_t$; that weaker condition is not part of this item. Policies are bounded stopping times, a disclosed pin.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 18, Theorem 1(b), condition (5); proof p. 31; application p. 33

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem theorem_1b (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    (h5 : ∀ (θ g v : ℝ), 0 < v → drift (BR u) θ v g ≤ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B)
    (T : Ω → ℝ≥0) (hT : IsFreeSamplePolicy (dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) T) :
    Integrable (revenue p u θ B T) P ∧
      ∫ ω, revenue p u θ B T ω ∂P ≤ BR u p.θ₀ p.σ₀sq := by sorry

end FreeSamples.Revenue
