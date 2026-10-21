-- Prove2me | Theorems.Thm_HackingInterval_ATE_theorem_4_max
-- name    : HackingInterval.ATE.theorem_4_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:16.590989+00:00
-- url     : https://prove2.me/theorems/ff2d67cd-84d5-42ea-9d57-0de11eda91c5
-- title:
--   Theorem 4, pp. 13–14 (PDF 14–15) — the solution of max x(new)ᵀβ s.t. Σ(yᵢ − xᵢᵀβ)² ≤ θ is β∗+ = β∗LS + μ̃Υ
-- statement:
--   Let $X$ be a finite real design matrix with linearly independent columns, let $Y$ be its outcome vector, and let $x^{(\mathrm{new})}\ne0$. Write $\beta^*_{\mathrm{LS}}=(X^\mathsf TX)^{-1}X^\mathsf TY$, $\mathrm{SSE}=\|Y-X\beta^*_{\mathrm{LS}}\|^2$, $\Upsilon=(X^\mathsf TX)^{-1}x^{(\mathrm{new})}$, and $\tilde\mu=\sqrt{\theta-\mathrm{SSE}}/\|X\Upsilon\|$. If $\theta\ge\mathrm{SSE}$, then the unique solution to the maximization problem in Theorem 4 is
--
--   $$\mathop{\mathrm{argmax}}_{\beta:\,\|Y-X\beta\|^2\le\theta}\;x^{(\mathrm{new})\mathsf T}\beta=\{\beta^*_{\mathrm{LS}}+\tilde\mu\Upsilon\}.$$
--
--   This is the general-design upper endpoint used when specializing Theorem 4 to the treatment coordinate.
--
--   **Formalization Note** Full column rank, feasible tolerance, and $x^{(\mathrm{new})}\ne0$ make the inverse and denominator meaningful and ensure that the optimizer is unique. The paper lists both signs but does not assign them to the two problems; the plus sign maximizes the linear objective.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), pp. 13–14 (PDF 14–15), Theorem 4, maximization half

import Mathlib
import Definitions.Def_HackingInterval_ATE_Design
open Matrix

namespace HackingInterval.ATE

theorem theorem_4_max {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (D : Design ι κ) (θ : ℝ) (xnew : κ → ℝ)
    (hrank : IsUnit (D.Xᵀ * D.X).det) (hθ : D.SSE ≤ θ) (hx : xnew ≠ 0) :
    ∀ β, D.IsMaxSol θ xnew β ↔ β = D.betaPlus θ xnew := by sorry

end HackingInterval.ATE
