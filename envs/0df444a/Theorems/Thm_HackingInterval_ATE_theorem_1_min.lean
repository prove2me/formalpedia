-- Prove2me | Theorems.Thm_HackingInterval_ATE_theorem_1_min
-- name    : HackingInterval.ATE.theorem_1_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:15.17992+00:00
-- url     : https://prove2.me/theorems/ce9806d4-ac3e-45a9-bbd3-be217bbf2184
-- title:
--   Theorem 1, eq. (17), p. 11 (PDF 12) — the solution of (15) is β∗0,min = β̃∗0,LS − √Vtt √(θ − SSE), β∗min = β∗LS − β∗0,min γ∗LS
-- statement:
--   Let $X$ contain the confounders, $w$ the zero-one treatment indicator, $Y$ the outcomes, and $\tilde X=[X,w]$. Suppose $\tilde X$ has linearly independent columns and the tolerance $\theta$ is at least the full-design residual sum of squares $\mathrm{SSE}$. With $\tilde\beta^*_{0,\mathrm{LS}}$ the treatment coordinate of the regression on $\tilde X$ and $V_{tt}$ its inverse-Gram diagonal entry, the unique solution of problem (15) is
--
--   $$\beta^*_{0,\min}=\tilde\beta^*_{0,\mathrm{LS}}-\sqrt{V_{tt}}\sqrt{\theta-\mathrm{SSE}},\qquad \beta^*_{\min}=\beta^*_{\mathrm{LS}}-\beta^*_{0,\min}\gamma^*_{\mathrm{LS}}.$$
--
--   Here $\beta^*_{\mathrm{LS}}$ regresses $Y$ on $X$ and $\gamma^*_{\mathrm{LS}}$ regresses $w$ on $X$. This equation gives both the lower interval endpoint and the confounder coefficients attaining it.
--
--   **Formalization Note** The paper prints SSE from the $X$-only regression. The full-design SSE used here corrects that false formula; the rank and tolerance assumptions make the inverse and square root meaningful.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), p. 11 (PDF 12), Theorem 1, eq. (17)

import Mathlib
import Definitions.Def_HackingInterval_ATE_Model
open Matrix

namespace HackingInterval.ATE

theorem theorem_1_min {n p : ℕ} (D : TreatData n p) (θ : ℝ)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hθ : D.SSE ≤ θ) :
    ∀ (β : Fin p → ℝ) (b0 : ℝ),
      D.IsSol15 θ β b0 ↔ β = D.betaMin θ ∧ b0 = D.beta0Min θ := by sorry

end HackingInterval.ATE
