-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_conjugate_maximizer_eq_gradient_readable
-- name    : FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:28.761638+00:00
-- url     : https://prove2.me/theorems/80335e95-bd3b-41ae-b542-89eb54c17879
-- title:
--   Conjugate Maximizer Equals Dual Gradient
-- statement:
--   This is the identification part of the dual-differentiability argument from Berman–Berndtsson, arXiv:1207.6128v1, Lemma 2.7 and Appendix 6, and is used for the first-variation framework of Cordero-Erausquin–Klartag, arXiv:1304.0630v1.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\varphi:E\to[-\infty,\infty]$ be a `ProperPotential`. Let $y$ lie in the interior of the set where the Legendre transform $\varphi^*$ is not $+\infty$, and assume $q\mapsto(\varphi^*(q)).\operatorname{toReal}$ is differentiable at $y$. If $z\in E$ satisfies
--
--   $$
--   \langle z,y\rangle-\varphi(z)=\varphi^*(y),
--   $$
--
--   then
--
--   $$
--   z=\nabla\big((\varphi^*)_{\mathbb R}\big)(y).
--   $$
--
--   The declaration is `conjugate_maximizer_eq_gradient_readable`. The primal potential need not be convex, differentiable, nonnegative, or finite everywhere; existence of a maximizer is not asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem conjugate_maximizer_eq_gradient
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E]
--       (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
--       {y : E} (hy : y ∈ interior {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
--       (hd : DifferentiableAt ℝ
--         (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
--       ∀ z : E,
--         (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y →
--         z = gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Next: [`exists_coercive_tilt_of_mem_interior_legendre_domain`](https://prove2.me/theorems/2a6ee0ab-9933-4999-9219-7fdf5606d335).
--
--   [Source excerpt, lines 43–52](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L43-L52) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L37-L196 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    {y : E} (hy : y ∈ interior {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ
      (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
    ∀ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y →
      z = gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y := by sorry
