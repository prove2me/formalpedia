-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_kt_one_dim_regret
-- name    : ModernOnlineLearning.ParameterFree.kt_one_dim_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:11.768005+00:00
-- url     : https://prove2.me/theorems/d6992d98-404d-4436-ae32-99e178b7a707
-- title:
--   §13.2.1, p. 214 — one-dimensional KT regret
-- statement:
--   Run the one-dimensional KT OCO algorithm with $\varepsilon>0$ and $L>0$ for $T\ge1$ rounds. Each chosen subgradient $g_t$ supports the loss $\ell_t$ at the prediction $x_t$ and satisfies $|g_t|\le L$. For every competitor $u\in\mathbb R$,
--   $$\sum_{t=1}^T\bigl(\ell_t(x_t)-\ell_t(u)\bigr)\le |u|L\sqrt{2T\ln\left(1+\frac{e|u|T}{\varepsilon}\right)}+\varepsilon L.$$
--
--   This per-coordinate guarantee is the direct input to the coordinate-wise bound.
--
--   **Formalization Note** The run also records full-space subdifferentiability of each loss. The positive-parameter and positive-horizon hypotheses make the displayed quotient and logarithm use their intended domains.
-- source:
--   Orabona, arXiv:1912.13213v10, §13.2.1, displayed KT regret guarantee, p. 214

import Mathlib
import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs

namespace ModernOnlineLearning.ParameterFree

/-- The displayed one-dimensional KT regret guarantee in §13.2.1, p. 214. -/
theorem kt_one_dim_regret (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (T : ℕ) (hT : 1 ≤ T) (ℓ : ℕ → ℝ → ℝ) (g x : ℕ → ℝ)
    (hrun : IsOneDKTRun ε L T ℓ g x) :
    ∀ u : ℝ,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        |u| * L * Real.sqrt
          (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * |u| * (T : ℝ) / ε)) + ε * L := by sorry

end ModernOnlineLearning.ParameterFree
