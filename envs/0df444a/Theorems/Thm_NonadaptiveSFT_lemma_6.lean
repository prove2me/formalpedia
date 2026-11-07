-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_6
-- name    : NonadaptiveSFT.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:21:56.317497+00:00
-- url     : https://prove2.me/theorems/827ee4a3-4ce8-40dd-9571-683496bc9911
-- title:
--   Lemma 6 — Ville's maximal inequality: $\Pr[\max_{0\le j\le r}Z_j\ge\lambda]\le\mathbb E[Z_0]/\lambda$
-- statement:
--   Let $(Z_j)_{j=0}^r$ be nonnegative integrable random variables adapted to a filtration $(\mathcal F_j)_{j=0}^r$ with $\mathbb E[Z_{j+1}\mid\mathcal F_j]\le Z_j$ for $0\le j<r$. Then for every $\lambda>0$,
--
--   $$\Pr\Big[\max_{0\le j\le r}Z_j\ge\lambda\Big]\le\frac{\mathbb E[Z_0]}\lambda,$$
--
--   and in particular the bound is $1/\lambda$ if $Z_0=1$.
--
--   The locator's analysis applies it to an exponential supermartingale along heavy paths and to a potential sum over retained nodes, with $\mathbb E[Z_0]\ne1$ in the second case.
--
--   Differences from the source:
--   - encoding: a finite process and filtration indexed by 0, …, r → processes and filtrations indexed by ℕ, with the supermartingale inequality for j < r only; reason: a finite family extends by Z_j = Z_r, F_j = F_r for j > r and satisfies every hypothesis; the conclusion involves j ≤ r only
--   - encoding: Z₀ = 1 → Z₀ = 1 almost surely; reason: equality of random variables is almost sure
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 6, p.20 (PDF p.22)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace NonadaptiveSFT

/-- **Lemma 6** (Ville's maximal inequality), p.20 (PDF p.22).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

Let `(Z_j)_{j=0}^r` be nonnegative integrable random variables adapted to a filtration
`(F_j)_{j=0}^r` with `E[Z_{j+1} | F_j] ≤ Z_j` for `0 ≤ j < r`. Then for every `λ > 0`,
`Pr[max_{0≤j≤r} Z_j ≥ λ] ≤ E[Z_0]/λ`; in particular, if `Z_0 = 1`, the bound is `1/λ`.

**Formalization Note.** The process and the filtration are indexed by `ℕ`; only `j ≤ r` enters the
supermartingale hypothesis and the conclusion. A finite family `(Z_j, F_j)_{j ≤ r}` is the case
`Z_j = Z_r`, `F_j = F_r` for `j > r`, which satisfies every hypothesis. The event
`max_{j ≤ r} Z_j ≥ λ` is written `∃ j ≤ r, λ ≤ Z_j`. Conditional expectation is Mathlib's `μ[·|F_j]`,
and the inequality holds almost surely; `Z_0 = 1` is read almost surely. -/
theorem lemma_6 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (r : ℕ) (hadapt : Adapted ℱ Z)
    (hnonneg : ∀ j ω, 0 ≤ Z j ω) (hint : ∀ j, Integrable (Z j) μ)
    (hsuper : ∀ j < r, μ[Z (j + 1) | ℱ j] ≤ᵐ[μ] Z j) :
    (∀ lam : ℝ, 0 < lam →
      (μ {ω | ∃ j ≤ r, lam ≤ Z j ω}).toReal ≤ (∫ ω, Z 0 ω ∂μ) / lam) ∧
    ((∀ᵐ ω ∂μ, Z 0 ω = 1) → ∀ lam : ℝ, 0 < lam →
      (μ {ω | ∃ j ≤ r, lam ≤ Z j ω}).toReal ≤ 1 / lam) := by sorry

end NonadaptiveSFT
