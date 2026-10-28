-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
-- name    : FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:11.391708+00:00
-- url     : https://prove2.me/theorems/72eb7aa6-074f-46cd-aef2-551ce162488e
-- title:
--   Near-Maximizers Concentrate Near the Legendre Gradient
-- statement:
--   This is a pointwise stability statement for Legendre maximizers.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and let $y$ lie in the interior of the finite domain of `legendre φ`. Assume that
--   $$q\mapsto(\operatorname{legendre}(\phi)(q))_{\mathrm{toReal}}$$
--   is differentiable at $y$. Then for every $\varepsilon>0$ there exists $\delta>0$ such that every $z\in E$ satisfying
--   $$\bigl((\operatorname{legendre}(\phi)(y))_{\mathrm{toReal}}-\delta\bigr)
--   \le \langle z,y\rangle-\phi(z)$$
--   obeys
--   $$\left\|z-\nabla\bigl((\operatorname{legendre}(\phi))_{\mathrm{toReal}}\bigr)(y)\right\|<\varepsilon.$$
--
--   The near-maximality condition is quantified directly over $z$; no maximizing sequence or selected maximizer is assumed. This is the concentration estimate used in first-variation arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_delta_nearMaximizer_norm_sub_gradient_lt
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E]
--       (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
--       (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
--       (hd : DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y) :
--       ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E,
--         (((legendre φ y).toReal - δ : ℝ) : EReal) ≤
--             (inner ℝ z y : EReal) - φ z →
--           ‖z - gradient (fun q : E => (legendre φ q).toReal) y‖ < ε
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Derivative`](https://prove2.me/theorems/a009d134-31d2-47e2-823a-2b8d35d6fdf8).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Next: [`hasDerivAt_legendre_add_smul_of_dualDifferentiable`](https://prove2.me/theorems/53a6ee6c-57c2-4889-bf33-e52e9986092d).
--
--   [Source excerpt, lines 36–45](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L36-L45) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L33-L232 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, declaration `FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E,
      (((legendre φ y).toReal - δ : ℝ) : EReal) ≤
          (inner ℝ z y : EReal) - φ z →
        ‖z - gradient (fun q : E => (legendre φ q).toReal) y‖ < ε := by sorry
