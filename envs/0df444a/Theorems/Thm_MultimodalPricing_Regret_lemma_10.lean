-- Prove2me | Theorems.Thm_MultimodalPricing_Regret_lemma_10
-- name    : MultimodalPricing.Regret.lemma_10
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:02:12.901349+00:00
-- url     : https://prove2.me/theorems/1a11465b-d26b-46e9-aa8c-b144bcf1411e
-- title:
--   Lemma 10 — uniform ellipsoid concentration as printed
-- statement:
--   Let $k,t\ge1$ and $0<\delta<1$. On any probability space with a predecision filtration, let $X_n\in\mathbb R^k$ be predictable and $\xi_n$ be next-step measurable, integrable centered increments: the integral of $\xi_n$ over every predecision measurable event is zero. Almost surely, for every $n<t$, $\|X_n\|_2\le\sqrt k$ and $|\xi_n|\le1$. The printed assertion is that, except on a set of outer probability at most $\delta$, simultaneously for every symmetric positive-definite real matrix $\Lambda$,
--   $$\sup_{z^\top\Lambda z\le1}|\sum_{n<t}\xi_n\langle X_n,z\rangle|\le\sqrt{2k\log(4kt/\delta)}+2.$$
--   This retains the all-SPD quantifier. It is false as printed: finding I1 gives the scalar counterexample; the target is preserved for proof or disproof.
--
--   Differences from the source:
--   - generalization: pricing features φ(pₙ) and centered demand noise → any predictable k-vector and bounded centered increment satisfying the printed norm and noise bounds; reason: every pricing instance embeds by taking Xₙ=φ(pₙ) and ξₙ=dₙ−f(pₙ)
--   - encoding: natural k,t in the logarithm → positive natural k,t; reason: excludes only the undefined zero-dimensional or zero-sample logarithm
--   - encoding: rounds 1 through t and vector coordinates 0 through k−1 → rounds in Finset.range t, ordered lists retaining repetitions, and vectors Fin k → ℝ; reason: reindexing changes no observation or coefficient
--   - encoding: with probability at least 1−δ or 1−O(1/T) → outer measure of the strict bad event at most δ or B/T; reason: agrees on measurable events and avoids assuming measurability of an uncountable supremum
--   - encoding: uniform supremum bound over every SPD matrix → failure means existence of an SPD matrix and a point of its ellipsoid exceeding the bound; reason: exact logical complement, with each ellipsoid nonempty and compact
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Lemma 10, printed/PDF p. 33; equation (23) and noise setup, p. 32

import Mathlib

open MeasureTheory Matrix
open scoped BigOperators

namespace MultimodalPricing.Regret

theorem lemma_10
    (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (info : Filtration ℕ mΩ) (X : ℕ → Ω → Fin k → ℝ) (ξ : ℕ → Ω → ℝ)
    (hX : ∀ n < t, Measurable[info n] (X n))
    (hξ : ∀ n < t, Measurable[info (n + 1)] (ξ n))
    (hbound : ∀ᵐ ω ∂μ, ∀ n < t,
      Real.sqrt (X n ω ⬝ᵥ X n ω) ≤ Real.sqrt k ∧ |ξ n ω| ≤ 1)
    (hint : ∀ n < t, Integrable (ξ n) μ)
    (hcenter : ∀ n < t, ∀ A : Set Ω, MeasurableSet[info n] A →
      (∫ ω in A, ξ n ω ∂μ) = 0) :
    μ {ω | ∃ Λ : Matrix (Fin k) (Fin k) ℝ, Λ.PosDef ∧
      ∃ z : Fin k → ℝ, z ⬝ᵥ (Λ *ᵥ z) ≤ 1 ∧
        Real.sqrt (2 * k * Real.log (4 * k * t / δ)) + 2 <
          |∑ n ∈ Finset.range t, ξ n ω * (X n ω ⬝ᵥ z)|} ≤ ENNReal.ofReal δ := by sorry

end MultimodalPricing.Regret
