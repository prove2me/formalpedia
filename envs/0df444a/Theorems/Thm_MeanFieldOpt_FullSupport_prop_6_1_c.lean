-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_prop_6_1_c
-- name    : MeanFieldOpt.FullSupport.prop_6_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:30:19.102096+00:00
-- url     : https://prove2.me/theorems/3814230e-6465-4b92-956a-bef84e6e4fc9
-- title:
--   Proposition 6.1(c) — $\|\Phi^{\gamma_1}-\Phi^{\gamma_2}\|_\infty\le\|\xi''(\gamma_1-\gamma_2)\|_1$ on $\mathsf{SF}_+$
-- statement:
--   Let $\xi$ be a mixture and $f_0$ an admissible terminal condition. If $\gamma_1, \gamma_2 \in \mathsf{SF}_+$ and $\Phi^{\gamma_1}, \Phi^{\gamma_2}$ are the corresponding Cole–Hopf solutions of the Parisi PDE (6.2), then
--
--   $$
--   \sup_{(t,x)\in[0,1]\times\mathbb R} \bigl|\Phi^{\gamma_1}(t,x) - \Phi^{\gamma_2}(t,x)\bigr| \;\le\; \int_0^1 \xi''(s)\,|\gamma_1(s) - \gamma_2(s)|\,ds .
--   $$
--
--   This Lipschitz estimate is what makes $\gamma \mapsto \Phi^\gamma$ extend by continuity from step functions to the whole space $\mathscr L$.
--
--   **Formalization Note** The sup norm is stated pointwise for every $t \in [0,1]$ and $x \in \mathbb R$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 23, Proposition 6.1(c)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_PhiSF

open MeasureTheory

namespace MeanFieldOpt.FullSupport

/-- Proposition 6.1 (c) (arXiv:2001.00904v1, p. 23): for `γ₁, γ₂ ∈ SF₊`,
`‖Φ^{γ₁} - Φ^{γ₂}‖_∞ ≤ ‖ξ''(γ₁ - γ₂)‖₁`, the sup norm over `[0,1] × ℝ`. -/
theorem prop_6_1_c (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (d₁ d₂ : SFData) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      |PhiSF ξ f₀ d₁ t x - PhiSF ξ f₀ d₂ t x| ≤
        ∫ s in Set.Ico (0 : ℝ) 1, ξ.d2 s * |d₁.toFun s - d₂.toFun s| := by sorry

end MeanFieldOpt.FullSupport
