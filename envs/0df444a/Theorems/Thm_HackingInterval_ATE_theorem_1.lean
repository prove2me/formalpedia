-- Prove2me | Theorems.Thm_HackingInterval_ATE_theorem_1
-- name    : HackingInterval.ATE.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:20.846352+00:00
-- url     : https://prove2.me/theorems/e40c80e9-03c9-4a19-b26c-94e959038a03
-- title:
--   Theorem 1, p. 11 (PDF 12) — the solutions of (14)/(15) are β∗0,max/min = β̃∗0,LS ± √Vtt √(θ − SSE), β∗max/min = β∗LS − β∗0,max/min γ∗LS (SSE corrected)
-- statement:
--   Let $X$ be the confounder matrix, $w$ the zero-one treatment indicator, $Y$ the outcome vector, and $\tilde X=[X,w]$. Suppose $\tilde X$ has linearly independent columns and $\theta$ is at least the full-design least-squares loss $\mathrm{SSE}$. Then the solution sets of the maximization and minimization problems (14) and (15) are exactly the following singleton coefficient pairs:
--
--   $$\begin{aligned}
--   \operatorname{argmax}_{L(\beta,\beta_0)\le\theta}\beta_0&=\{(\beta^*_{\mathrm{LS}}-\beta^*_{0,\max}\gamma^*_{\mathrm{LS}},\,\beta^*_{0,\max})\},\\
--   \operatorname{argmin}_{L(\beta,\beta_0)\le\theta}\beta_0&=\{(\beta^*_{\mathrm{LS}}-\beta^*_{0,\min}\gamma^*_{\mathrm{LS}},\,\beta^*_{0,\min})\},\\
--   \beta^*_{0,\max/\min}&=\tilde\beta^*_{0,\mathrm{LS}}\pm\sqrt{V_{tt}}\sqrt{\theta-\mathrm{SSE}}.
--   \end{aligned}$$
--
--   Here $\tilde\beta^*_{0,\mathrm{LS}}$ is the treatment coefficient of regression on $\tilde X$, $V_{tt}$ the treatment diagonal of $(\tilde X^\mathsf T\tilde X)^{-1}$, $\beta^*_{\mathrm{LS}}$ the regression of $Y$ on $X$, and $\gamma^*_{\mathrm{LS}}$ the regression of $w$ on $X$. The theorem characterizes the entire interval and both attaining models.
--
--   **Formalization Note** The paper's printed SSE uses the regression on $X$ alone, which gives incorrect endpoints. The formal statement uses the residual loss of regression on $\tilde X$; with the printed SSE the formula is false: in a planning check with $n=30$, $p=3$ and $\theta=1.1\,\mathrm{SSE}_X$, the numerical maximum of $\beta_0$ is $4.47403$, the formula with the $\tilde X$ residual gives $4.47403$, and the formula with the printed SSE gives $2.95592$. Full column rank and $\theta\ge\mathrm{SSE}$ are the necessary implicit domain conditions.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), p. 11 (PDF 12), Theorem 1, eqs. (14)–(17)

import Mathlib
import Definitions.Def_HackingInterval_ATE_Model
open Matrix

namespace HackingInterval.ATE

theorem theorem_1 {n p : ℕ} (D : TreatData n p) (θ : ℝ)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hθ : D.SSE ≤ θ) :
    (∀ (β : Fin p → ℝ) (b0 : ℝ),
      D.IsSol14 θ β b0 ↔ β = D.betaMax θ ∧ b0 = D.beta0Max θ) ∧
    (∀ (β : Fin p → ℝ) (b0 : ℝ),
      D.IsSol15 θ β b0 ↔ β = D.betaMin θ ∧ b0 = D.beta0Min θ) := by sorry

end HackingInterval.ATE
