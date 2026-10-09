-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_lemma_4
-- name    : NonconvexAG.StochComposite.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:51.63207+00:00
-- url     : https://prove2.me/theorems/3de4af21-7f66-48b1-b18c-6fa7488b9287
-- title:
--   Lemma 4 — the gradient mapping 𝒢(x, ·, c) is 1-Lipschitz
-- statement:
--   Let $\mathcal X$ be convex with domain $K$, and let $\mathcal P$ be its prox map (2.37), with the gradient mapping $\mathcal G(x,y,c)=\frac1c[x-\mathcal P(x,y,c)]$ of (2.38). Then for every $x\in\mathbb R^n$, every $c>0$ and all $y_1,y_2\in\mathbb R^n$,
--   $$\|\mathcal G(x,y_1,c)-\mathcal G(x,y_2,c)\|\le\|y_1-y_2\|.$$
--
--   In §3.2 this lemma transfers the error of the stochastic gradient $\bar G_k$ to the stochastic gradient mapping, giving (3.29).
--
--   **Formalization Note** The paper leaves $c>0$ implicit (the prox map (2.37) is defined for $c\in(0,+\infty)$); it is stated. Convexity of $\mathcal X$ on its domain $K$ is the paper's standing assumption on $\mathcal X$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 10, Lemma 4

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- Lemma 4 (p. 10): for a convex `𝒳` with domain `K` and its prox map `𝒫` (2.37), the gradient
mapping `𝒢(x, ·, c)` of (2.38) is 1-Lipschitz for every `x` and every `c > 0`. -/
theorem lemma_4 {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) :
    ∀ x y1 y2 : E n, ∀ c : ℝ, 0 < c →
      ‖gradMap P x y1 c - gradMap P x y2 c‖ ≤ ‖y1 - y2‖ := by sorry

end NonconvexAG.StochComposite
