-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasDerivAt_legendre_add_smul_of_dualDifferentiable_readable
-- name    : FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:19.650556+00:00
-- url     : https://prove2.me/theorems/53a6ee6c-57c2-4889-bf33-e52e9986092d
-- title:
--   Pointwise Legendre First Variation
-- statement:
--   This is a pointwise first-variation formula for the Legendre transform under a bounded continuous perturbation.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\phi:E\to\overline{\mathbb{R}}$ be a proper lower-semicontinuous potential. Let $y$ lie in the interior of the finite domain of $\phi^*$, and assume $q\mapsto(\phi^*(q)).toReal$ is differentiable at $y$. Let $b:E\to\mathbb{R}$ be continuous and assume $|b|$ is bounded above. Then the map
--
--   $$
--   t\longmapsto\bigl(\phi+t b\bigr)^*(y).toReal
--   $$
--
--   has derivative at $0$ equal to
--
--   $$
--   -b\bigl(\nabla(\phi^*).toReal(y)\bigr).
--   $$
--
--   Here $(\phi+t b)(z)$ denotes $\phi(z)+(t b(z):\overline{\mathbb{R}})$. No differentiability or global finiteness of $\phi$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_legendre_add_smul_of_dualDifferentiable
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E]
--       (φ : E → EReal) (hφ : ProperPotential φ)
--       (hlsc : LowerSemicontinuous φ) (y : E)
--       (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
--       (hd : DifferentiableAt ℝ (fun q => (legendre φ q).toReal) y)
--       (b : E → ℝ) (hb : Continuous b)
--       (hbounded : BddAbove (Set.range fun z : E => |b z|)) :
--       HasDerivAt
--         (fun t : ℝ =>
--           (legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y).toReal)
--         (-b (gradient (fun q => (legendre φ q).toReal) y)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Derivative`](https://prove2.me/theorems/a009d134-31d2-47e2-823a-2b8d35d6fdf8).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`exists_delta_nearMaximizer_norm_sub_gradient_lt`](https://prove2.me/theorems/72eb7aa6-074f-46cd-aef2-551ce162488e), [`exists_legendre_maximizer_with_gradient_identity`](https://prove2.me/theorems/0a4c46db-2543-480e-9c88-e7e91f832b89), [`legendre_bounded_perturbation_finite_curve`](https://prove2.me/theorems/f81ed50e-1e1f-44d9-a9cd-afd086601533).
--
--   Previous: [`exists_delta_nearMaximizer_norm_sub_gradient_lt`](https://prove2.me/theorems/72eb7aa6-074f-46cd-aef2-551ce162488e).
--
--   [Source excerpt, lines 245–257](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L245-L257) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L242-L436 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, declaration `FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q => (legendre φ q).toReal) y)
    (b : E → ℝ) (hb : Continuous b)
    (hbounded : BddAbove (Set.range fun z : E => |b z|)) :
    HasDerivAt
      (fun t : ℝ =>
        (legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y).toReal)
      (-b (gradient (fun q => (legendre φ q).toReal) y)) 0 := by sorry
