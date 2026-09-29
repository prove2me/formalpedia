-- Prove2me | Theorems.Thm_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
-- name    : MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/478f56f3-c430-54e7-be84-b9d1b7117bc9
-- title:
--   Gram-normalised Lebesgue measure of a parallelepiped
-- statement:
--   Let $V$ be a finite-dimensional real vector space, equipped with a Hausdorff topological additive group structure for which scalar multiplication is continuous, and with its Borel $\sigma$-algebra, and let $B \colon V \times V \to \mathbb{R}$ be an $\mathbb{R}$-bilinear form (given as an element of $V \to_{\mathbb{R}} V \to_{\mathbb{R}} \mathbb{R}$). Let $n_1, n_2$ be natural numbers and let $e \colon \mathrm{Fin}\,n_1 \to V$ and $f \colon \mathrm{Fin}\,n_2 \to V$ be two families of vectors, each linearly independent over $\mathbb{R}$, and assume that they span the same subspace: $\operatorname{span}_{\mathbb{R}}(\operatorname{range} e) = \operatorname{span}_{\mathbb{R}}(\operatorname{range} f)$. Consider the measure on $V$ obtained by pushing Lebesgue measure on $\mathbb{R}^{n_1}$ forward along the coordinate map $a \mapsto \sum_i a_i e_i$ and scaling it by $\sqrt{\lvert \det (B(e_i,e_j))_{i,j} \rvert}$ (as an element of $[0,\infty]$ via `ENNReal.ofReal`). The assertion is that this measure assigns to the half-open parallelepiped $\{\sum_i a_i f_i : 0 \le a_i < 1\}$, the image of $\prod_{i} [0,1)$ under $a \mapsto \sum_i a_i f_i$, the value $\sqrt{\lvert \det (B(f_i,f_j))_{i,j} \rvert}$. In particular no relation between $n_1$ and $n_2$ is assumed; it follows from the equality of spans.
--
--   The statement expresses that the Gram-normalised measure of a subspace $W \subseteq V$ attached to $B$ does not depend on the chosen spanning family, in the concrete form: the covolume of the lattice $\bigoplus_i \mathbb{Z} f_i$ inside $W$, measured by the Gram-normalised measure written down using any other basis $e$ of $W$, equals the square root of the absolute value of the Gram determinant of $f$. It is used in the construction of normalised Haar measures and in the computation of Gram determinants of integral bases after base change in the automorphic-forms part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n₁ n₂ : ℕ} (e : Fin n₁ → V) (f : Fin n₂ → V)
    (he : LinearIndependent ℝ e) (hf : LinearIndependent ℝ f)
    (hspan : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range f)) :
    ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e i) (e j)).det|)) •
        Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e i) volume)
      ((fun a : Fin n₂ → ℝ => ∑ i, a i • f i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) =
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (f i) (f j)).det|) := by sorry
