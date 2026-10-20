-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_prop_ec_3_3_ii
-- name    : NonconcaveUtil.Viscosity.prop_ec_3_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:46.644051+00:00
-- url     : https://prove2.me/theorems/e4970cc6-b00c-490a-a94e-f2fbdc3f06f3
-- title:
--   Proposition EC.3.3(ii) — concave-envelope terminal limit
-- statement:
--   If the portfolio interval is unbounded, the value function approaches the concave envelope $\hat U$ of the utility at maturity:
--
--   $$\lim_{(t,\zeta)\to(T-,w)}V(t,\zeta)=\hat U(w).$$
--
--   This identifies the terminal target in the unbounded-portfolio viscosity condition.
--
--   **Formalization Note** The statement is the one-stock constant-coefficient specialization of the e-companion's multivariate proposition. The limit approaches through $D=[0,T)\times(B,\infty)$, and $w=B$ is included only for finite boundary utility. The value is asserted finite on $D$ before conversion to reals.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. ec18 (PDF 50), Proposition EC.3.3(ii)

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- Proposition EC.3.3(ii), p. ec18, in the one-stock model: unbounded
portfolio access concavifies the terminal utility. -/
theorem prop_ec_3_3_ii (mk : Market) (hmk : mk.Standing) (hunbound : ¬mk.Bounded)
    (U : ℝ → ℝ) (pHat : ℝ) (bc : BdryCase)
    (hU : Assumption31 mk U pHat bc)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (𝓑 : ℝ≥0 → Ω → ℝ)
    (h𝓑 : IsFBrownian P ℱ 𝓑) (w : ℝ)
    (hw : mk.B < w ∨ (w = mk.B ∧ bc = .finite)) :
    (∀ q ∈ mk.D, valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊤ ∧
      valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊥) ∧
    Tendsto (fun q : ℝ × ℝ => (valueFn mk U P ℱ 𝓑 q.1 q.2).toReal)
      (𝓝[mk.D] (mk.T, w)) (𝓝 (Uhat mk U bc w)) := by sorry

end NonconcaveUtil.Viscosity
