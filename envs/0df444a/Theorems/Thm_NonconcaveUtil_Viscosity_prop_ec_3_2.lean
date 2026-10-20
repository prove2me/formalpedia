-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_prop_ec_3_2
-- name    : NonconcaveUtil.Viscosity.prop_ec_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:52.968442+00:00
-- url     : https://prove2.me/theorems/aadd89ed-7dfd-4200-b934-3004ba6c5dcf
-- title:
--   Proposition EC.3.2 — liquidation boundary behavior of the value function
-- statement:
--   As time and wealth approach a point $(\bar t,B)$ before maturity, the value function approaches $U(B)$ when that value is finite. In the singular case $B=0$, its difference from the corresponding CRRA value approaches zero:
--
--   $$V(t,w)\to U(B),\quad\text{or}\quad V(t,w)-V_{\mathrm{CRRA}}(t,w)\to0.$$
--
--   This result verifies the boundary clause used in the viscosity solution definition.
--
--   **Formalization Note** This is the one-stock constant-coefficient specialization of the e-companion result. Limits are taken from $D=[0,T)\times(B,\infty)$. The assertion includes finiteness of the value on $D$ so conversion from extended reals cannot turn infinity into Lean's default real value.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. ec15 (PDF 47), Proposition EC.3.2, (EC.47)

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- Proposition EC.3.2, p. ec15, in the one-stock constant-coefficient model:
the value approaches the prescribed liquidation boundary. -/
theorem prop_ec_3_2 (mk : Market) (hmk : mk.Standing) (U : ℝ → ℝ)
    (pHat : ℝ) (bc : BdryCase) (hU : Assumption31 mk U pHat bc)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (𝓑 : ℝ≥0 → Ω → ℝ)
    (h𝓑 : IsFBrownian P ℱ 𝓑) (tbar : ℝ) (htbar : tbar ∈ Set.Ico 0 mk.T) :
    (∀ q ∈ mk.D, valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊤ ∧
      valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊥) ∧
    match bc with
      | .finite =>
          Tendsto (fun q : ℝ × ℝ => (valueFn mk U P ℱ 𝓑 q.1 q.2).toReal)
            (𝓝[mk.D] (tbar, mk.B)) (𝓝 (U mk.B))
      | .crra pTilde A1 A2 =>
          Tendsto (fun q : ℝ × ℝ =>
            (valueFn mk U P ℱ 𝓑 q.1 q.2).toReal -
              VCRRA mk pTilde A1 A2 q.1 q.2)
            (𝓝[mk.D] (tbar, 0)) (𝓝 0) := by sorry

end NonconcaveUtil.Viscosity
