-- Prove2me | Theorems.Thm_NonconvexAG_Composite_lemma_5
-- name    : NonconvexAG.Composite.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:27.592216+00:00
-- url     : https://prove2.me/theorems/551acd9a-6188-4f5f-bc0b-35dc2228bd94
-- title:
--   Lemma 5 — −(L_f/2)‖y−x‖² ≤ Ψ(y) − Ψ(x) − ⟨∇Ψ(x), y−x⟩ ≤ (L_Ψ/2)‖y−x‖²
-- statement:
--   Let $\Psi=f+h$ as in (1.3): $f:\mathbb R^n\to\mathbb R$ is differentiable with $L_f$-Lipschitz gradient (possibly nonconvex), $h:\mathbb R^n\to\mathbb R$ is convex and differentiable with $L_h$-Lipschitz gradient, $\nabla\Psi=\nabla f+\nabla h$ and $L_\Psi=L_f+L_h$. Then for all $x,y\in\mathbb R^n$
--   $$-\frac{L_f}2\|y-x\|^2\le\Psi(y)-\Psi(x)-\langle\nabla\Psi(x),y-x\rangle\le\frac{L_\Psi}2\|y-x\|^2 .$$
--
--   The upper bound is the usual quadratic bound for an $L_\Psi$-smooth function; the lower bound improves the constant from $L_\Psi$ to $L_f$, because the convex part $h$ contributes only a nonnegative term. This is what lets the analysis of Algorithm 2 depend on $L_f$, and reduce to the convex rate when $L_f=0$.
--
--   **Formalization Note** Smoothness is `IsBetaSmooth f gf Lf` (differentiable with gradient map `gf`, `Lf ≥ 0`, gradient `Lf`-Lipschitz), and likewise for `h`; $\Psi$ and $\nabla\Psi$ are written out as `f y + h y` and `gf x + gh x`.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 11, Lemma 5 (2.43); the setting is (1.3), p. 2

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- Lemma 5 (p. 11), (2.43): `Ψ = f + h` with `f ∈ C^{1,1}_{L_f}`, `h ∈ C^{1,1}_{L_h}` convex,
`∇Ψ = ∇f + ∇h` and `L_Ψ = L_f + L_h`. -/
theorem lemma_5 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h) :
    ∀ x y : NonconvexAG.Smooth.E n,
      -(Lf / 2) * ‖y - x‖ ^ 2 ≤ (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ∧
        (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ≤ (Lf + Lh) / 2 * ‖y - x‖ ^ 2 := by sorry
end NonconvexAG.Composite
