-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_proposition_16
-- name    : HeteroRetire.Boundary.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:12.937981+00:00
-- url     : https://prove2.me/theorems/b013134d-845a-4671-8a88-7c04d6f1459f
-- title:
--   Proposition 16, p. 17 — retirement and working regions separated by b
-- statement:
--   The free boundary $b(t)$ divides the positive dual states at every $t\in[0,T)$:
--   $$
--   \mathcal R=\{(t,y)\in\mathcal S:y\le b(t)\},\qquad
--   \mathcal C=\{(t,y)\in\mathcal S:y>b(t)\}.
--   $$
--
--   Thus the optimal retirement decision is described by a single threshold in the dual state. The same proposition compares boundaries under changes to income and labor cost; that clause is stated separately.
--
--   **Formalization Note** Independence from the individual's utility is built into the definition of $\mathbb W$ used here, which contains no utility function. The identity with the paper's original definition (24) is outside this mission.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, Proposition 16, p. 17

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proposition 16, p. 17: the retirement and working regions are
separated by the free boundary. -/
theorem proposition_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z) :
    retireRegion P 𝔽 M Z =
      {p : ℝ × ℝ | p.1 ∈ Ico 0 M.T ∧ 0 < p.2 ∧ (p.2 : EReal) ≤ bdry P 𝔽 M Z p.1} ∧
    workRegion P 𝔽 M Z =
      {p : ℝ × ℝ | p.1 ∈ Ico 0 M.T ∧ 0 < p.2 ∧ bdry P 𝔽 M Z p.1 < (p.2 : EReal)} := by sorry

end HeteroRetire.Boundary
