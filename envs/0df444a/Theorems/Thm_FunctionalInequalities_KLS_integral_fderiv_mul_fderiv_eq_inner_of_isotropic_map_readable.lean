-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
-- name    : FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:32.465663+00:00
-- url     : https://prove2.me/theorems/5232fd28-307b-473d-a267-0276d096b8b7
-- title:
--   Gradient Second Moments Under an Isotropic Pushforward
-- statement:
--   This formalizes the second-moment identity in Lemma 2.3 of Letwin (arXiv:2607.24164v1).
--
--   Let $\nu$ be a probability measure on a finite-dimensional real inner-product space, let $\phi:E\to\mathbb{R}$, and assume `gradient φ` is measurable. If the pushforward $(\nabla\phi)_*\nu$ is isotropic, then for every $u,v\in E$,
--
--   $$
--   \int D\phi(x)[u]D\phi(x)[v]\,d\nu(x)=\langle u,v\rangle.
--   $$
--
--   The conclusion uses the isotropy of the pushforward only; no convexity or regularity of $\phi$ beyond the stated measurable gradient representation is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map
--       (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
--       (hiso : Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
--       ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Previous: [`Isotropic.map_linearIsometryEquiv`](https://prove2.me/theorems/2a04e022-1e2a-44a3-9511-86cbce831c79) · Next: [`Isotropic.integral_norm_sq`](https://prove2.me/theorems/d8804772-cf20-4fb4-8ca9-55643b773065).
--
--   [Source excerpt, lines 145–148](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Isotropic.lean#L145-L148) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.3. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Isotropic.lean#L143-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Isotropic`, declaration `FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
    (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
    (hiso : Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
    ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫ := by sorry
