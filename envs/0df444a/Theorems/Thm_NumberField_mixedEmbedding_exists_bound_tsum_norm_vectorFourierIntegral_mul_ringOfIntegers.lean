-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers
-- name    : NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/25a9b033-5245-50a2-9c75-e941dbee5761
-- title:
--   Uniform lattice-sum decay for Fourier transforms on the mixed space
-- statement:
--   Let $K$ be a number field, with mixed space $E = \mathrm{mixedSpace}\,K = \prod_{w\text{ real}}\mathbb{R}\times\prod_{w\text{ complex}}\mathbb{C}$, canonical embedding $\iota =$ `NumberField.mixedEmbedding K` of $K$ into $E$, and the multiplicative norm `NumberField.mixedEmbedding.norm` on $E$; let $N$ be a natural number. The assertion is that there exist a finite set $s$ of pairs of natural numbers and a real $C \ge 0$ such that for every Schwartz function $g \in \mathcal S(E,\mathbb{C})$ and every $a \in E$ with $\mathrm{Nm}(a) \ge 1$, writing $\widehat g$ for `VectorFourier.fourierIntegral` of $g$ taken with respect to the additive character $\mathbf e$, Lebesgue measure on $E$ and the pairing $\mathrm{Algebra.traceForm}_{\mathbb R}(E)$, namely $(x,y)\mapsto \mathrm{Tr}_{E/\mathbb R}(xy)$: first, the family $\xi \mapsto \lVert \widehat g(a\,\iota(\xi))\rVert$ indexed by $\xi \in \mathcal{O}_K$ is summable; and second, the sum over the nonzero $\xi \in \mathcal{O}_K$ satisfies $$\sum_{\xi \neq 0} \lVert \widehat g(a\,\iota(\xi))\rVert \le C \cdot \bigl(\sup_{(k,n)\in s} p_{k,n}\bigr)(g)\cdot \mathrm{Nm}(a)^{-N},$$ where $p_{k,n}$ is Mathlib's Schwartz seminorm family on $\mathcal S(E,\mathbb{C})$ and $\mathrm{Nm}(a)^{-N}$ is $(\mathrm{Nm}(a)^{-1})^{N}$. The data $s$ and $C$ depend only on $K$ and $N$, uniformly in $g$ and $a$.
--
--   This is the uniform decay estimate for lattice sums of the Fourier transform of a test function on the Minkowski (mixed) space of $K$, in the shape in which it is consumed after Poisson summation, where only the nonzero Fourier modes contribute. It is used by [`NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv`](thm.html#NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv), the variant in which $a$ enters through multiplication by its inverse.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap NumberField Classical

theorem NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (g : 𝓢(NumberField.mixedEmbedding.mixedSpace K, ℂ))
        (a : NumberField.mixedEmbedding.mixedSpace K),
        1 ≤ NumberField.mixedEmbedding.norm a →
          Summable (fun ξ : 𝓞 K ↦ ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K)) g
              (a * NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K)) g
              (a * NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖
            ≤ C * (s.sup (schwartzSeminormFamily ℝ (NumberField.mixedEmbedding.mixedSpace K) ℂ)) g *
                (NumberField.mixedEmbedding.norm a)⁻¹ ^ N := by sorry
