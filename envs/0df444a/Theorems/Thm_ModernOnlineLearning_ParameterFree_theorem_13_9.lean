-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_theorem_13_9
-- name    : ModernOnlineLearning.ParameterFree.theorem_13_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:50.857512+00:00
-- url     : https://prove2.me/theorems/990b78a4-de0f-4102-99b1-a090cc627cd3
-- title:
--   Theorem 13.9, p. 215 — coordinate-wise KT parameter-free regret
-- statement:
--   Let $d\ge1$, $\varepsilon>0$, $L_\infty>0$, and $T\ge1$. Run Algorithm 13.3 on subdifferentiable losses $\ell_t:\mathbb R^d\to\mathbb R$, choosing a full-space subgradient $g_t$ at each prediction $x_t$ with $\|g_t\|_\infty\le L_\infty$. For every $u\in\mathbb R^d$, both inequalities hold:
--   $$\sum_{t=1}^T\bigl(\ell_t(x_t)-\ell_t(u)\bigr)\le L_\infty\sum_{i=1}^d |u_i|\sqrt{2T\ln\left(1+\frac{e|u_i|T}{\varepsilon}\right)}+d\varepsilon L_\infty\le\|u\|_1L_\infty\sqrt{2T\ln\left(1+\frac{e\|u\|_\infty T}{\varepsilon}\right)}+d\varepsilon L_\infty.$$
--
--   The result gives one parameter-free regret bound for each coordinate and the resulting bound in $\ell_1$ and $\ell_\infty$ norms.
--
--   **Formalization Note** Vectors are functions on `Fin d`; their function-space norm is the sup norm. The run predicate enforces Algorithm 13.3's exact update and bounds each selected subgradient coordinate. Positivity of $\varepsilon$, $L_\infty$, and $T$ is explicit.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 13.9, p. 215

import Mathlib
import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs

namespace ModernOnlineLearning.ParameterFree

/-- Theorem 13.9, p. 215: both coordinate-wise and norm-form regret bounds. -/
theorem theorem_13_9 (d : ℕ) (hd : 0 < d) (ε L : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → (Fin d → ℝ) → ℝ) (g x : ℕ → Fin d → ℝ)
    (hrun : IsCoordKTRun ε L T ℓ g x) :
    ∀ u : Fin d → ℝ,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        L * (∑ i : Fin d, |u i| * Real.sqrt
          (2 * (T : ℝ) * Real.log
            (1 + Real.exp 1 * |u i| * (T : ℝ) / ε))) + (d : ℝ) * ε * L ∧
      L * (∑ i : Fin d, |u i| * Real.sqrt
        (2 * (T : ℝ) * Real.log
          (1 + Real.exp 1 * |u i| * (T : ℝ) / ε))) + (d : ℝ) * ε * L ≤
        (∑ i : Fin d, |u i|) * L * Real.sqrt
          (2 * (T : ℝ) * Real.log
            (1 + Real.exp 1 * ‖u‖ * (T : ℝ) / ε)) + (d : ℝ) * ε * L := by sorry

end ModernOnlineLearning.ParameterFree
