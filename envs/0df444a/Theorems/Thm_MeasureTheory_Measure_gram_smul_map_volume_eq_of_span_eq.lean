-- Prove2me | Theorems.Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq
-- name    : MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/3569b30c-aadd-59b9-b3e7-ce319ab37702
-- title:
--   Basis independence of the Gram-normalised Lebesgue measure
-- statement:
--   Let $V$ be a real topological vector space (an additive commutative group with an $\mathbb{R}$-module structure, a topology making addition and scalar multiplication continuous, and a measurable space structure which is the Borel structure of the topology), and let $B$ be an $\mathbb{R}$-bilinear form on $V$. Let $n, n'$ be natural numbers and let $e : \mathrm{Fin}\,n \to V$ and $e' : \mathrm{Fin}\,n' \to V$ be families of vectors, each assumed linearly independent over $\mathbb{R}$, and assume that the $\mathbb{R}$-span of the range of $e'$ equals the $\mathbb{R}$-span of the range of $e$. Then the two measures on $V$ obtained by pushing forward Lebesgue measure on $\mathbb{R}^{n'}$, respectively $\mathbb{R}^{n}$, along the coordinate maps $c \mapsto \sum_i c_i e'_i$ and $c \mapsto \sum_i c_i e_i$, and scaling by the extended-nonnegative-real numbers $\sqrt{|\det (B(e'_i,e'_j))_{i,j}|}$ and $\sqrt{|\det (B(e_i,e_j))_{i,j}|}$ respectively, coincide. In other words, the measure $\sqrt{|\det \mathrm{Gram}_B(f)|}\cdot (c \mapsto \sum_i c_i f_i)_*\mathrm{Leb}$ depends only on the span of the linearly independent family $f$, not on $f$ itself.
--
--   This is the statement that the Gram-normalised Lebesgue measure attached to a finite-dimensional subspace of $V$ and a bilinear form $B$ is intrinsic, i.e. independent of the chosen basis; it is the standard normalisation used for Haar measures on the archimedean components of adelic groups. It is used in the comparison of Haar measures on products of archimedean places with the discriminant-normalised measure, and in the computation of integrals of archimedean identifications in the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (B : LinearMap.BilinForm ℝ V) {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V)
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n' => B (e' i) (e' j)).det|)) •
        Measure.map (fun c : Fin n' → ℝ => ∑ i, c i • e' i) volume =
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => B (e i) (e j)).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume := by sorry
