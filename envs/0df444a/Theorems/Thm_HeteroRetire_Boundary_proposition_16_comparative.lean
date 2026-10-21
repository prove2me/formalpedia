-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_proposition_16_comparative
-- name    : HeteroRetire.Boundary.proposition_16_comparative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:08.617394+00:00
-- url     : https://prove2.me/theorems/9bfe5abd-9e7a-4402-b2e8-4442d373be7d
-- title:
--   Proposition 16, p. 17 — income and labor-cost comparative statics
-- statement:
--   Compare two markets with the same horizons, interest rate, discount rate, excess returns, volatility and market price of risk. Let their income and labor-cost functions be $(I_1,L_1)$ and $(I_2,L_2)$. If $I_2(t)\le I_1(t)$ and $L_1(t)\le L_2(t)$ for every $t\in[0,T]$, then
--   $$
--   b_1(t)\le b_2(t)\qquad (0\le t\le T).
--   $$
--
--   Holding one pair equal gives each comparison in Proposition 16: higher income or lower labor cost lowers the retirement threshold.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, Proposition 16, p. 17

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proposition 16, p. 17: larger income and smaller labor cost
lower the boundary, holding the other market data fixed. -/
theorem proposition_16_comparative {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (I₂ L₂ : ℝ → ℝ)
    (hM₂ : ({M with I := I₂, L := L₂} : Market n).Standing)
    (hI : ∀ t ∈ Icc 0 M.T, I₂ t ≤ M.I t)
    (hL : ∀ t ∈ Icc 0 M.T, M.L t ≤ L₂ t) :
    ∀ t ∈ Icc 0 M.T,
      bdry P 𝔽 M Z t ≤
        bdry P 𝔽 ({M with I := I₂, L := L₂} : Market n) Z t := by sorry

end HeteroRetire.Boundary
