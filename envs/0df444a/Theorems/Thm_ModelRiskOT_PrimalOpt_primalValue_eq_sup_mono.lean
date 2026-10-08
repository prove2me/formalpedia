-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_primalValue_eq_sup_mono
-- name    : ModelRiskOT.PrimalOpt.primalValue_eq_sup_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:04:45.188974+00:00
-- url     : https://prove2.me/theorems/77117af9-e360-4c1f-84c5-afa97c5f1aa0
-- title:
--   §5 display (p. 26) — I = sup over Φ′_{µ,δ}
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $\delta>0$, and let $c$ and $f$ satisfy (A1) and (A2). Then the primal value is unchanged if the supremum is taken over monotone plans only:
--   $$I=\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}=\sup\{I(\pi):\pi\in\Phi'_{\mu,\delta}\}.$$
--
--   This is the starting point of the proof of Proposition 9, which picks a maximizing sequence inside $\Phi'_{\mu,\delta}$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 26, §5, Additional notation (display)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PrimalFeasibleMono

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **§5, Additional notation** (p. 26). Under (A1) and (A2),
`I = sup{I(π) : π ∈ Φ_{μ,δ}} = sup{I(π) : π ∈ Φ′_{μ,δ}}`. -/
theorem primalValue_eq_sup_mono {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S)
    [IsProbabilityMeasure μ] (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c)
    (hA2 : AssumptionA2 f μ) :
    ModelRiskOT.Duality.primalValue c f μ δ = ⨆ π ∈ primalFeasibleMono c f μ δ, ModelRiskOT.Duality.primalObj f π := by sorry

end ModelRiskOT.PrimalOpt
