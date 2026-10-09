-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_lemma_5
-- name    : NonconvexAG.StochComposite.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:01.093985+00:00
-- url     : https://prove2.me/theorems/40c4e105-7328-4996-85d0-ec6a4f5c181b
-- title:
--   Lemma 5 — −(L_f/2)‖y − x‖² ≤ Ψ(y) − Ψ(x) − ⟨∇Ψ(x), y − x⟩ ≤ (L_Ψ/2)‖y − x‖²
-- statement:
--   Let $\Psi=f+h$, where $f:\mathbb R^n\to\mathbb R$ is differentiable with $L_f$-Lipschitz gradient (possibly nonconvex) and $h:\mathbb R^n\to\mathbb R$ is convex and differentiable with $L_h$-Lipschitz gradient, and let $L_\Psi=L_f+L_h$. Then for all $x,y\in\mathbb R^n$
--   $$-\frac{L_f}2\|y-x\|^2\le\Psi(y)-\Psi(x)-\langle\nabla\Psi(x),y-x\rangle\le\frac{L_\Psi}2\|y-x\|^2.$$
--
--   The lower bound measures how far $\Psi$ is from convex in terms of $L_f$ alone; it is what makes the final bound of Theorem 4 depend on $L_f$ rather than on $L_\Psi$ in its non-convexity term.
--
--   **Formalization Note** $\nabla\Psi=\nabla f+\nabla h$ is written out. Restated from mission 2 of this series because drafts cannot import one another.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 11, Lemma 5, (2.43)

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

/-- Lemma 5 (p. 11), (2.43): `Ψ = f + h` with `f ∈ C^{1,1}_{L_f}`, `h ∈ C^{1,1}_{L_h}` convex,
`∇Ψ = ∇f + ∇h` and `L_Ψ = L_f + L_h`. -/
theorem lemma_5 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h) :
    ∀ x y : E n,
      -(Lf / 2) * ‖y - x‖ ^ 2 ≤ (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ∧
        (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ≤
          (Lf + Lh) / 2 * ‖y - x‖ ^ 2 := by sorry

end NonconvexAG.StochComposite
