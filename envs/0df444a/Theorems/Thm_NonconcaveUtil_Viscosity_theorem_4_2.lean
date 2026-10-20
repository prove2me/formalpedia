-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_theorem_4_2
-- name    : NonconcaveUtil.Viscosity.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:46.129671+00:00
-- url     : https://prove2.me/theorems/4e5c14e4-6c2d-47eb-a2ef-ab54d674c8d9
-- title:
--   Theorem 4.2 — the value function is the unique viscosity solution
-- statement:
--   For the bounded or unbounded portfolio market of Section 3 and a utility satisfying Assumption 3.1, the stochastic-control value function $V$ is finite on the interior, satisfies Definition A.1 for the HJB equation (14), and is continuous before maturity. Every viscosity solution in the growth class of Theorem 4.1 agrees with $V$:
--
--   $$V'(t,w)=V(t,w)\qquad(0<t<T,\ w>B).$$
--
--   The result ties the portfolio optimization problem to the PDE characterization with its liquidation boundary and terminal asymptotics.
--
--   **Formalization Note** The theorem is quantified over filtered probability spaces carrying Brownian motion, with the value built from admissible wealth processes. The finite value assertion makes conversion from extended reals meaningful. Uniqueness is in the growth class used by Theorem 4.1. Continuity is on $D=[0,T)\times(B,\infty)$; values at $w=B$ are governed by the separate boundary condition.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. 12 (PDF 12), Theorem 4.2

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- Theorem 4.2, p. 12: the stochastic-control value is the unique solution
in the comparison growth class, and is continuous before maturity. -/
theorem theorem_4_2 (mk : Market) (hmk : mk.Standing) (U : ℝ → ℝ)
    (pHat : ℝ) (bc : BdryCase) (hU : Assumption31 mk U pHat bc)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (𝓑 : ℝ≥0 → Ω → ℝ)
    (h𝓑 : IsFBrownian P ℱ 𝓑) :
    let V : ℝ → ℝ → ℝ := fun t w => (valueFn mk U P ℱ 𝓑 t w).toReal
    (∀ q ∈ mk.D, valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊤ ∧
      valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊥) ∧
    IsViscositySolution mk U bc V ∧
    (∀ V' : ℝ → ℝ → ℝ, IsViscositySolution mk U bc V' →
      (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        ∀ q ∈ mk.D, V' q.1 q.2 ≤ C₁ * q.2 ^ pHat + C₂) →
      ∀ t ∈ Set.Ioo 0 mk.T, ∀ w > mk.B, V' t w = V t w) ∧
    ContinuousOn (Function.uncurry V) mk.D := by sorry

end NonconcaveUtil.Viscosity
