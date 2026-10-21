-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_prop16_mono_y
-- name    : HeteroRetire.Boundary.prop16_mono_y
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:11.513256+00:00
-- url     : https://prove2.me/theorems/38991ba3-4012-443c-8ca7-5029e3fd4063
-- title:
--   Proof of Proposition 16, p. 39 — dual stopping value increases in the dual state
-- statement:
--   Fix a time $t\in[0,T)$. Under the standing market and dual-noise assumptions, the dual stopping value is nondecreasing on positive states:
--   $$
--   0<y_1\le y_2\quad\Longrightarrow\quad \mathbb W(t,y_1)\le\mathbb W(t,y_2).
--   $$
--
--   This is the comparison in the proof of Proposition 16 that supports a threshold description of retirement.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, proof of Proposition 16, p. 39

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proof of Proposition 16, p. 39: 𝕎 is increasing in the dual state. -/
theorem prop16_mono_y {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (t : ℝ) (ht : t ∈ Ico 0 M.T) :
    MonotoneOn (Wdual P 𝔽 M Z t) (Ioi 0) := by sorry

end HeteroRetire.Boundary
