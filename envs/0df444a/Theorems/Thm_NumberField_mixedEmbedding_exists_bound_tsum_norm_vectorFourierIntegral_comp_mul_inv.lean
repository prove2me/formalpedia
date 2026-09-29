-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
-- name    : NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/79ebb3c2-3664-5d16-8b63-5d01446085fd
-- title:
--   Dilation form of lattice decay for Fourier transforms on the mixed space
-- statement:
--   Let $K$ be a number field, with mixed space $E = \mathrm{mixedSpace}\,K = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, canonical embedding $\iota =$ `NumberField.mixedEmbedding K` of $K$ into $E$, and the multiplicative norm $\mathrm{Nm} =$ `NumberField.mixedEmbedding.norm` on $E$; let $N$ be a natural number. For $h \colon E \to \mathbb{C}$ write $\widehat{h}$ for `VectorFourier.fourierIntegral` taken with respect to the character $\mathbf{e}(x) = e^{2\pi i x}$, Lebesgue measure on $E$, and the pairing given by the trace form `Algebra.traceForm ℝ E` of the $\mathbb{R}$-algebra $E$. The assertion is that there exist a finite set $s \subseteq \mathbb{N} \times \mathbb{N}$ of Schwartz seminorm indices and a real constant $C \ge 0$ such that for every Schwartz function $g \in \mathcal{S}(E, \mathbb{C})$ and every unit $a$ of the ring $E$ with $\mathrm{Nm}(a) \ge 1$, putting $g_a(x) = g(a^{-1} x)$: first, the family $\xi \mapsto \lVert \widehat{g_a}(\iota \xi) \rVert$ indexed by $\xi \in \mathcal{O}_K$ is summable; and second, $$\sum_{\xi \in \mathcal{O}_K,\ \xi \neq 0} \bigl\lVert \widehat{g_a}(\iota \xi) \bigr\rVert \le C \cdot \bigl(\sup_{(k,n) \in s} p_{k,n}\bigr)(g) \cdot \mathrm{Nm}(a)^{-N},$$ where $p_{k,n}$ is Mathlib's `schwartzSeminormFamily` on $\mathcal{S}(E, \mathbb{C})$ and the right-hand factor is the $N$-th power of $\mathrm{Nm}(a)^{-1}$. The finite set $s$ and the constant $C$ are uniform in $g$ and in $a$.
--
--   This is the dilated form of the decay of lattice sums of Fourier transforms on the mixed space: a bound for the Fourier transform of a test function conjugated by an element $a$ of $E^{\times}$ of norm at least $1$, summed over the nonzero integers of $K$, with the gain $\mathrm{Nm}(a)^{-N}$ for arbitrary prescribed $N$ and a constant depending only on finitely many Schwartz seminorms. It is obtained from the undilated statement [`NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers`](thm.html#NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers), and is used in the estimates on unipotent terms and constant terms of automorphic forms that enter the Siegel-domain truncation arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap NumberField Classical

theorem NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (g : 𝓢(NumberField.mixedEmbedding.mixedSpace K, ℂ))
        (a : (NumberField.mixedEmbedding.mixedSpace K)ˣ),
        1 ≤ NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) →
          Summable (fun ξ : 𝓞 K ↦ ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖
            ≤ C * (s.sup (schwartzSeminormFamily ℝ (NumberField.mixedEmbedding.mixedSpace K) ℂ)) g *
                (NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K))⁻¹ ^ N := by sorry
