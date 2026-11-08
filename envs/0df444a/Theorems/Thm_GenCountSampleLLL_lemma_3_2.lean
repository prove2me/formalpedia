-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_3_2
-- name    : GenCountSampleLLL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:39:30.341206+00:00
-- url     : https://prove2.me/theorems/49fe33ee-1108-47ce-92c1-8e71911d0250
-- title:
--   Lemma 3.2, p.11 — moments of $\mathrm{Recip}(Y)=\sum_{k=0}^{\mathbf N}4^k\prod_{j\le k}Y_j$, $\mathbf N\sim\mathrm{Geom}(3/4)$
-- statement:
--   Let $Y_1,Y_2,\dots$ be independent copies of a real random variable $Y$ with mean $r\ge0$ and second moment $v<1/4$, and choose $\mathbf N\sim\mathrm{Geom}(3/4)$ independently (mass $\tfrac34(\tfrac14)^k$ at $k$). Set $\mathrm{Recip}(Y)=\sum_{k=0}^{\mathbf N}4^k\prod_{j=1}^kY_j$. Then $\mathrm{Recip}(Y)$, $\mathrm{Recip}(Y)^2$ and $\mathbf N$ are integrable and
--   $$
--   \mathbb E\,\mathrm{Recip}(Y)=\frac1{1-r},\qquad\mathbb E\,\mathrm{Recip}(Y)^2=\frac{1+r}{(1-r)(1-4v)},\qquad\mathbb E\,\mathbf N=\frac13.
--   $$
--
--   This is the reciprocal estimator of the factors $(1-r_{\mathcal E,b})^{-1}$ in the 2-tree expansion.
--
--   Differences from the source:
--   - encoding: Y₁, Y₂, …, ∏_{j=1}^{k} Y_j → Y 0, Y 1, …, ∏_{j<k} Y j, each identically distributed with Y 0; reason: re-indexing from 0
--   - reading: "independent copies", "independently choose" 𝐍 → `iIndepFun Y`, `IndepFun N (j ↦ Y j)`, measurable Y j and N; reason: the standard meaning
--   - reading: "second moment v", 𝔼Recip(Y) = …, 𝔼𝐍 = 1/3 → `MemLp (Y 0) 2` with ∫ Y 0² = v; integrability of Recip(Y), Recip(Y)² and 𝐍 stated together with the values; reason: a second moment presupposes E Y² < ∞, and an expectation statement presupposes integrability; a Bochner integral of a non-integrable function is 0
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 3.2, p.11

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace GenCountSampleLLL

/-- Lemma 3.2, p.11 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)). Let `Y₁, Y₂, …` be independent copies of a real random
variable `Y` with mean `r ≥ 0` and second moment `v < 1/4`, and independently `N ∼ Geom(3/4)`
(mass `(3/4)(1/4)^k` at `k`). Then `Recip(Y) = Σ_{k=0}^{N} 4^k ∏_{j=1}^{k} Y_j` satisfies
`E Recip(Y) = 1/(1 − r)`, `E Recip(Y)² = (1 + r)/((1 − r)(1 − 4v))`, and `E N = 1/3`.

**Formalization Note.** The copies are indexed from `0`: `Y 0, Y 1, …`, with
`∏_{j<k} Y j` for the page's `∏_{j=1}^{k} Y_j`; each is distributed as `Y 0`. "Second moment
`v`" presupposes `E Y² < ∞` (`MemLp (Y 0) 2`). Integrability of `Recip(Y)`, `Recip(Y)²` and `N`
is part of the conclusion, so the Bochner integrals are not junk values. -/
theorem lemma_3_2 {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (hYm : ∀ j, Measurable (Y j)) (hNm : Measurable N)
    (hind : ProbabilityTheory.iIndepFun Y μ)
    (hindN : ProbabilityTheory.IndepFun N (fun ω j => Y j ω) μ)
    (hid : ∀ j, ProbabilityTheory.IdentDistrib (Y j) (Y 0) μ μ)
    (hL2 : MeasureTheory.MemLp (Y 0) 2 μ) (r v : ℝ)
    (hr : ∫ ω, Y 0 ω ∂μ = r) (hr0 : 0 ≤ r) (hv : ∫ ω, Y 0 ω ^ 2 ∂μ = v) (hv4 : v < 1 / 4)
    (hN : ∀ k : ℕ, μ {ω | N ω = k} = ENNReal.ofReal (3 / 4 * (1 / 4) ^ k)) :
    MeasureTheory.Integrable
        (fun ω => ∑ k ∈ Finset.range (N ω + 1), (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, Y j ω) μ ∧
      ∫ ω, (∑ k ∈ Finset.range (N ω + 1), (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, Y j ω) ∂μ =
        1 / (1 - r) ∧
      MeasureTheory.Integrable
        (fun ω => (∑ k ∈ Finset.range (N ω + 1), (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, Y j ω) ^ 2)
        μ ∧
      ∫ ω, (∑ k ∈ Finset.range (N ω + 1), (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, Y j ω) ^ 2 ∂μ =
        (1 + r) / ((1 - r) * (1 - 4 * v)) ∧
      MeasureTheory.Integrable (fun ω => (N ω : ℝ)) μ ∧
      ∫ ω, (N ω : ℝ) ∂μ = 1 / 3 := by sorry

end GenCountSampleLLL
