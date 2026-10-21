-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_proposition_17
-- name    : HeteroRetire.Boundary.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:14.66298+00:00
-- url     : https://prove2.me/theorems/d72316b3-9d2a-49e1-9204-940c9a18f447
-- title:
--   Proposition 17, p. 17 (preterminal) — boundary bounded by labor cost over income
-- statement:
--   At each preterminal time $t\in[0,T)$, the retirement boundary obeys
--   $$
--   b(t)\le\frac{L(t)}{I(t)}.
--   $$
--
--   This gives an explicit bound in terms of the two labor coefficients, independent of the individual's utility.
--
--   **Formalization Note** The printed proposition includes $t=T$, but the paper's definition gives $b(T)=+\infty$ because $\mathbb W(T,y)=0$ for every $y$. The theorem uses the paper's state-space range $[0,T)$.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, Proposition 17, p. 17

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proposition 17, p. 17, on the paper's preterminal state space. -/
theorem proposition_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (t : ℝ) (ht : t ∈ Ico 0 M.T) :
    bdry P 𝔽 M Z t ≤ ((M.L t / M.I t : ℝ) : EReal) := by sorry

end HeteroRetire.Boundary
