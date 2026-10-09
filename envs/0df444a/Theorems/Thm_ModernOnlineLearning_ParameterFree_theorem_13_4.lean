-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_theorem_13_4
-- name    : ModernOnlineLearning.ParameterFree.theorem_13_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:22.888686+00:00
-- url     : https://prove2.me/theorems/b23b1008-3345-4378-bbaf-f07b5ad8c02b
-- title:
--   Theorem 13.4, p. 210 — KT wealth lower bound for continuous coins
-- statement:
--   Start the KT bettor with wealth $\varepsilon>0$ and give it outcomes $c_t\in[-1,1]$ for rounds $1,\ldots,T$, where $T\ge1$. Write $C_T=\sum_{t=1}^T c_t$. Then
--   $$\operatorname{Wealth}_T\ge\frac{\varepsilon 2^T\Gamma((T+1+C_T)/2)\Gamma((T+1-C_T)/2)}{\pi\Gamma(T+1)}\ge\varepsilon\exp\left(\frac{C_T^2}{2T}-\frac{\ln T}{2}-1\right).$$
--
--   This is the continuous-coin wealth guarantee used to derive KT's one-dimensional regret bound.
--
--   **Formalization Note** The hypothesis $T\ge1$ gives a defined real denominator in the exponential expression and follows the intended domain of the printed bound.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 13.4, p. 210

import Mathlib
import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs

namespace ModernOnlineLearning.ParameterFree

/-- Theorem 13.4, p. 210: continuous-coin KT wealth and its exponential lower bound. -/
theorem theorem_13_4 (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1 ≤ T)
    (c : ℕ → ℝ)
    (hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1) :
    let C : ℝ := ∑ t ∈ Finset.Icc 1 T, c t
    ktPotential ε T C ≤ ktWealth ε c T ∧
      ε * Real.exp (C ^ 2 / (2 * (T : ℝ)) - Real.log (T : ℝ) / 2 - 1) ≤
        ktPotential ε T C := by sorry

end ModernOnlineLearning.ParameterFree
