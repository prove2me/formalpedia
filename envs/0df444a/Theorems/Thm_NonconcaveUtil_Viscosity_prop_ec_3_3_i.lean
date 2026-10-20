-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_prop_ec_3_3_i
-- name    : NonconcaveUtil.Viscosity.prop_ec_3_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:38.569556+00:00
-- url     : https://prove2.me/theorems/b55dce78-6301-4463-8ba5-3390b0863589
-- title:
--   Proposition EC.3.3(i), equation EC.55 — bounded-portfolio terminal profile
-- statement:
--   Under bounded portfolio weights, the value function has the paper's terminal profile at a wealth $w$ in the utility domain. Writing $U(w-)$ for its left limit, $\Phi$ for the standard normal distribution function, and $L=\sigma\max\{u,-d\}$, the limit is
--
--   $$V(t,\zeta)-U(w-)-2\Phi\!\left(\frac{\min\{0,\log(\zeta/w)\}}{L\sqrt{T-t}}\right)\bigl(U(w)-U(w-)\bigr)\longrightarrow0$$
--
--   as $(t,\zeta)\to(T-,w)$. This is the terminal condition needed when utility may jump.
--
--   **Formalization Note** The e-companion's multivariate result is specialized to one stock and constant coefficients, as in its own equation EC.55. The source convention $U(B-)=U(B)$ is used at a finite liquidation boundary. The result includes finiteness of the control value on $D$.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. ec18 (PDF 50), Proposition EC.3.3(i), constant-coefficient form (EC.55)

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- Proposition EC.3.3(i), equation EC.55, p. ec18: the special terminal
profile for a bounded portfolio set and constant coefficients. -/
theorem prop_ec_3_3_i (mk : Market) (hmk : mk.Standing) (hbound : mk.Bounded)
    (U : ℝ → ℝ) (pHat : ℝ) (bc : BdryCase)
    (hU : Assumption31 mk U pHat bc)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (𝓑 : ℝ≥0 → Ω → ℝ)
    (h𝓑 : IsFBrownian P ℱ 𝓑) (w : ℝ)
    (hw : mk.B < w ∨ (w = mk.B ∧ bc = .finite)) :
    (∀ q ∈ mk.D, valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊤ ∧
      valueFn mk U P ℱ 𝓑 q.1 q.2 ≠ ⊥) ∧
    Tendsto (fun q : ℝ × ℝ =>
      (valueFn mk U P ℱ 𝓑 q.1 q.2).toReal -
        terminalProfile mk U bc w q.1 q.2)
      (𝓝[mk.D] (mk.T, w)) (𝓝 0) := by sorry

end NonconcaveUtil.Viscosity
