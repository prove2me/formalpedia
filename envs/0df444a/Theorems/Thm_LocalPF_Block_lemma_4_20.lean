-- Prove2me | Theorems.Thm_LocalPF_Block_lemma_4_20
-- name    : LocalPF.Block.lemma_4_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:16.035977+00:00
-- url     : https://prove2.me/theorems/91b26c15-803c-4f57-824e-f12a292a4b8d
-- title:
--   Lemma 4.20, p. 58 — product of empirical measures: |||µ^{⊗d} − µ̂^{⊗d}||| ≤ 4d/√N
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathbb S$, let $d\ge0$ and $N\ge1$, and let $X_1,\dots,X_N$ be i.i.d. with law $\mu$, with empirical measure $\hat\mu=\frac1N\sum_{k=1}^N\delta_{X_k}$. Then
--   $$|||\mu^{\otimes d}-\hat\mu^{\otimes d}|||\le\frac{4d}{\sqrt N},$$
--   that is, for every measurable $f:\mathbb S^d\to\mathbb R$ with $|f|\le1$,
--   $$\mathbf E\Big[\Big|\mu^{\otimes d}(f)-\frac1{N^d}\sum_{k_1,\dots,k_d=1}^Nf(X_{k_1},\dots,X_{k_d})\Big|^2\Big]\le\frac{16d^2}{N}.$$
--
--   This V-statistic estimate controls the sampling error of the product of block marginals of an empirical measure, which is what the blocking step produces.
--
--   **Formalization Note** $\hat\mu^{\otimes d}(f)=N^{-d}\sum_{k_1,\dots,k_d}f(X_{k_1},\dots,X_{k_d})$ is the paper's own formula (proof, p. 58). The $|||\cdot|||$ norm is written in the "for every test function" form with the square cleared; the expectation is a lower Lebesgue integral of a nonnegative quantity. Stated on an arbitrary measurable space.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 58, Lemma 4.20

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Lemma 4.20 (p. 58): `|||µ^{⊗d} − µ̂^{⊗d}||| ≤ 4d/√N`, in the `∀ f` form with the square
cleared, where `µ̂^{⊗d}(f) = N^{-d} Σ_{k_1,…,k_d} f(X_{k_1}, …, X_{k_d})`. -/
theorem lemma_4_20 {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (d N : ℕ) (hN : 1 ≤ N) (f : (Fin d → S) → ℝ) (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1) :
    ∫⁻ X : Fin N → S, ENNReal.ofReal ((∫ z, f z ∂(Measure.pi fun _ : Fin d => μ) -
        ((N : ℝ) ^ d)⁻¹ * ∑ k : Fin d → Fin N, f (X ∘ k)) ^ 2)
      ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal ((4 * d / Real.sqrt N) ^ 2) := by sorry

end LocalPF.Block
