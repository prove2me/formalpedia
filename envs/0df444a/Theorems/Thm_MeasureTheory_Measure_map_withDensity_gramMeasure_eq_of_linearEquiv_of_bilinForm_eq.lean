-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
-- name    : MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/4909c314-8c3a-5632-aefb-6d96904ed2f8
-- title:
--   Gram-normalised measure transported by a form-preserving automorphism
-- statement:
--   Let $V$ be a finite-dimensional real vector space which is a Hausdorff topological additive group with continuous scalar multiplication, equipped with its Borel $\sigma$-algebra. Let $B : V \to V \to \mathbb{R}$ be an $\mathbb{R}$-bilinear map, and let $\Phi : V \simeq V$ be an $\mathbb{R}$-linear automorphism with $B(\Phi x, \Phi y) = B(x,y)$ for all $x, y \in V$. Let $e_1 : \mathrm{Fin}\,n_1 \to V$ and $e_2 : \mathrm{Fin}\,n_2 \to V$ be linearly independent families (the cardinalities $n_1, n_2$ are a priori unrelated) such that the image under $\Phi$ of the span of the range of $e_2$ equals the span of the range of $e_1$. Let $\rho : V \to [0,\infty]$ be measurable and $\Phi$-invariant, $\rho(\Phi x) = \rho(x)$ for all $x$. For a family $e$ of length $n$ write $\mu_e$ for the pushforward of Lebesgue measure on $\mathbb{R}^n$ along $a \mapsto \sum_i a_i e_i$, and $G_e = \sqrt{\bigl|\det\bigl(B(e_i,e_j)\bigr)_{i,j}\bigr|}$, viewed in $[0,\infty]$ via `ENNReal.ofReal`. Then the pushforward along $\Phi$ of the measure $(G_{e_2} \cdot \mu_{e_2})$ with density $\rho$ equals $(G_{e_1} \cdot \mu_{e_1})$ with density $\rho$.
--
--   The measure $G_e \cdot \mu_e$ is the Gram normalisation, by the form $B$, of Lebesgue measure on the subspace spanned by $e$; the statement says that this normalised measure, weighted by a $\Phi$-invariant density, depends only on the subspace and is carried by a $B$-isometry of $V$ to the corresponding measure on the image subspace. It is used in the archimedean comparison of twisted and untwisted orbital integrals, and in a result identifying the Gram-normalised measure of the image of a product of intervals for two families with the same span.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V ≃ₗ[ℝ] V) (hΦ : ∀ x y : V, B (Φ x) (Φ y) = B x y)
    {n₁ n₂ : ℕ} (e₁ : Fin n₁ → V) (e₂ : Fin n₂ → V)
    (h₁ : LinearIndependent ℝ e₁) (h₂ : LinearIndependent ℝ e₂)
    (hspan : (Submodule.span ℝ (Set.range e₂)).map (Φ : V →ₗ[ℝ] V) = Submodule.span ℝ (Set.range e₁))
    (ρ : V → ENNReal) (hρm : Measurable ρ) (hρ : ∀ x : V, ρ (Φ x) = ρ x) :
    Measure.map Φ
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
            Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ) =
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e₁ i) (e₁ j)).det|)) •
          Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity ρ := by sorry
