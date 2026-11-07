-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_5
-- name    : NonadaptiveSFT.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:39.990014+00:00
-- url     : https://prove2.me/theorems/e8a3fa8b-0f80-4a19-aaf3-622aa428c59d
-- title:
--   Lemma 5 — median of means: $\Pr[N\ge\frac{r+1}2]\le\binom r{(r+1)/2}p^{(r+1)/2}\le\frac14(4p)^{(r+1)/2}$ and $\Pr[|\lambda-x|\ge\sqrt2\,\omega]\le\frac14(4p)^{(r+1)/2}$
-- statement:
--   Let $r\ge1$ be odd, on any probability space.
--
--   1. Let $0\le p\le1$ and let $E_1,\dots,E_r$ be independent events with $\Pr[E_i]\le p$; let $N$ be the number of events that occur. Then
--
--   $$\Pr\Big[N\ge\tfrac{r+1}2\Big]\le\binom r{(r+1)/2}p^{(r+1)/2}\le\tfrac14(4p)^{(r+1)/2}.$$
--
--   2. Let $x\in\mathbb C$, $\nu\ge0$, $\omega>0$, and $v\ge1$ an integer. Let $\xi_{i,b}$ ($i\in[r]$, $b\in[v]$) be independent complex random variables with $\mathbb E[\xi_{i,b}]=x$ and $\mathbb E|\xi_{i,b}-x|^2\le\nu$, let $\mu_i=\frac1v\sum_b\xi_{i,b}$, and let $\lambda$ be the coordinatewise median of $\mu_1,\dots,\mu_r$. With $p=\min\{1,\nu/(v\omega^2)\}$,
--
--   $$\Pr\big[|\lambda-x|\ge\sqrt2\,\omega\big]\le\binom r{(r+1)/2}p^{(r+1)/2}\le\tfrac14(4p)^{(r+1)/2}.$$
--
--   This is the amplification step used by the decision test, the locator's verification and the final coefficient estimation.
--
--   **Formalization Note** The count of item 1 and the radius of item 2 are renamed to avoid the group order $N$ and the root of unity.
--
--   Differences from the source:
--   - encoding: E[ξ_{i,b}] = x and E[|ξ_{i,b} − x|²] ≤ ν → ξ_{i,b} and |ξ_{i,b} − x|² integrable, with these integrals; reason: the expectations are assumed to exist; a Lean integral of a non-integrable function is 0
--   - encoding: events and complex random variables → measurable sets and measurable maps into ℂ; reason: the meaning of event and random variable
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 5, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Fourier

open MeasureTheory ProbabilityTheory

namespace NonadaptiveSFT

open Classical in
/-- **Lemma 5** (Median of means), p.19 (PDF p.21).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

Let `r ≥ 1` be odd and `μ` a probability measure.
1. If `0 ≤ p ≤ 1` and `E_1, …, E_r` are independent events with `Pr[E_i] ≤ p`, and `N` counts the
   events that occur, then `Pr[N ≥ (r+1)/2] ≤ C(r, (r+1)/2) p^{(r+1)/2} ≤ ¼(4p)^{(r+1)/2}`.
2. If `x ∈ ℂ`, `ν ≥ 0`, `ω > 0`, `v ≥ 1`, and `ξ_{i,b}` (`i ∈ [r]`, `b ∈ [v]`) are independent complex
   random variables with `E[ξ_{i,b}] = x` and `E|ξ_{i,b} − x|² ≤ ν`, `µ_i = (1/v)Σ_b ξ_{i,b}`, and `λ` is
   the coordinatewise median of the `µ_i`, then with `p = min{1, ν/(vω²)}`,
   `Pr[|λ − x| ≥ √2 ω] ≤ C(r, (r+1)/2) p^{(r+1)/2} ≤ ¼(4p)^{(r+1)/2}`.

**Formalization Note.** "Holds on any probability space" (p.20): `Ω` is arbitrary. The page's names
`N` (a count) and `ω` (a positive real) are `count` and `w` here. The independent indices `[r] × [v]`
are `Fin r × Fin v`. `E[ξ] = x` and `E|ξ − x|² ≤ ν` are written with the integrability of `ξ` and of
`|ξ − x|²` stated, since a Bochner integral of a non-integrable function is `0`. The median is
`NonadaptiveSFT.cmedian` (real and imaginary medians, the `((r+1)/2)`-th order statistic). -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : ℕ) (hr : Odd r) :
    (∀ (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ (E : Fin r → Set Ω), (∀ i, MeasurableSet (E i)) →
      iIndepSet E μ → (∀ i, (μ (E i)).toReal ≤ p) →
      let count : Ω → ℕ := fun ω => (Finset.univ.filter fun i => ω ∈ E i).card
      (μ {ω | (r + 1) / 2 ≤ count ω}).toReal ≤ (r.choose ((r + 1) / 2) : ℝ) * p ^ ((r + 1) / 2) ∧
      (r.choose ((r + 1) / 2) : ℝ) * p ^ ((r + 1) / 2) ≤ 1 / 4 * (4 * p) ^ ((r + 1) / 2)) ∧
    (∀ (x : ℂ) (ν w : ℝ), 0 ≤ ν → 0 < w → ∀ (v : ℕ), 1 ≤ v →
      ∀ ξ : Fin r × Fin v → Ω → ℂ, (∀ ib, Measurable (ξ ib)) → iIndepFun ξ μ →
      (∀ ib, Integrable (ξ ib) μ) → (∀ ib, ∫ ω, ξ ib ω ∂μ = x) →
      (∀ ib, Integrable (fun ω => ‖ξ ib ω - x‖ ^ 2) μ) →
      (∀ ib, ∫ ω, ‖ξ ib ω - x‖ ^ 2 ∂μ ≤ ν) →
      let mean : Fin r → Ω → ℂ := fun i ω => (1 / (v : ℂ)) * ∑ b, ξ (i, b) ω
      let lam : Ω → ℂ := fun ω => cmedian fun i => mean i ω
      let p : ℝ := min 1 (ν / (v * w ^ 2))
      (μ {ω | Real.sqrt 2 * w ≤ ‖lam ω - x‖}).toReal ≤
          (r.choose ((r + 1) / 2) : ℝ) * p ^ ((r + 1) / 2) ∧
        (r.choose ((r + 1) / 2) : ℝ) * p ^ ((r + 1) / 2) ≤ 1 / 4 * (4 * p) ^ ((r + 1) / 2)) := by sorry

end NonadaptiveSFT
