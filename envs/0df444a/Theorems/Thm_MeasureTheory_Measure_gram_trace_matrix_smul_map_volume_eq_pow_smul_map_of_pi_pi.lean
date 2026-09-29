-- Prove2me | Theorems.Thm_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
-- name    : MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/8dc0a765-ff78-5acb-b674-0dc5231b924d
-- title:
--   Gram measure of the trace form on matrix algebras
-- statement:
--   Let $R$ be a commutative normed ring which is a normed $\mathbb{R}$-algebra, carrying its Borel $\sigma$-algebra, let $\iota$ be a finite type, and equip $\mathrm{Matrix}\,\iota\,\iota\,R$ with its Borel $\sigma$-algebra. Let $m \in \mathbb{N}$ and let $b : \mathrm{Fin}\,m \to R$ be $\mathbb{R}$-linearly independent with $\mathbb{R}$-span all of $R$. Let $\mu$ be a $\sigma$-finite measure on $R$ and $\kappa \in [0,\infty]$ with $\kappa \neq \infty$, and assume that the Gram-normalised Lebesgue measure of $b$ for the trace form of $R$ equals $\kappa \cdot \mu$, i.e. $\mathrm{ofReal}\bigl(\sqrt{|\det(\mathrm{Tr}_{R/\mathbb{R}}(b_a b_{a'}))_{a,a'}|}\bigr)$ times the pushforward of Lebesgue measure on $\mathrm{Fin}\,m \to \mathbb{R}$ under $c \mapsto \sum_a c_a \cdot b_a$ is $\kappa \cdot \mu$. Then for every $n \in \mathbb{N}$ and every $\mathbb{R}$-linearly independent family $e : \mathrm{Fin}\,n \to \mathrm{Matrix}\,\iota\,\iota\,R$ whose $\mathbb{R}$-span is all of $\mathrm{Matrix}\,\iota\,\iota\,R$, the quantity $\mathrm{ofReal}\bigl(\sqrt{|\det(\mathrm{Tr}_{R/\mathbb{R}}\,\mathrm{tr}(e_i e_j))_{i,j}|}\bigr)$ times the pushforward of Lebesgue measure on $\mathrm{Fin}\,n \to \mathbb{R}$ under $c \mapsto \sum_i c_i \cdot e_i$ equals $\kappa^{|\iota| \cdot |\iota|}$ times the pushforward under `Matrix.of` of the iterated product measure $\mathrm{pi}_{\iota}\,\mathrm{pi}_{\iota}\,\mu$ on $\iota \to \iota \to R$.
--
--   This transfers a Gram-determinant normalisation of Lebesgue measure from a finite-dimensional commutative real algebra $R$ to the matrix algebra $M_\iota(R)$ with its real trace form $(X,Y) \mapsto \mathrm{Tr}_{R/\mathbb{R}}\,\mathrm{tr}(XY)$, identifying the resulting measure with an entrywise product measure up to the factor $\kappa^{|\iota|^2}$; it is invoked in [`AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing`](thm.html#AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing), where the archimedean Haar measure on matrices over the infinite adele ring of a number field must be written as a product of measures on the coordinates. The hypotheses on $e$ are for an arbitrary spanning linearly independent family, the independence of the Gram-normalised measure from the chosen family being supplied by [`MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq`](thm.html#MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
    (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [MeasurableSpace R] [BorelSpace R]
    (ι : Type) [Fintype ι] [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    (m : ℕ) (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤)
    (μ : Measure R) [SigmaFinite μ] (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hμ : (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ R (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume = κ • μ)
    (n : ℕ) (e : Fin n → Matrix ι ι R) (he : LinearIndependent ℝ e)
    (hesp : Submodule.span ℝ (Set.range e) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
          Algebra.trace ℝ R (Matrix.trace (e i * e j))).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume =
      κ ^ (Fintype.card ι * Fintype.card ι) •
        Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
          (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ) := by sorry
