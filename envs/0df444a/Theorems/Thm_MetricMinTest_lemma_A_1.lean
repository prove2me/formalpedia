-- Prove2me | Theorems.Thm_MetricMinTest_lemma_A_1
-- name    : MetricMinTest.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:12.519863+00:00
-- url     : https://prove2.me/theorems/3fd933a3-6d06-4f76-9b80-09658f08748b
-- title:
--   Lemma A.1, p.21 — one-stream threshold test: error bounds and $\mathbb E\min\{T,N\}\le2(\beta+\eta)/\eta^2$
-- statement:
--   Let $X_1,X_2,\dots$ be independent random variables with values in $[-1,1]$, each of mean $\mu$ (identical laws are not required). For a threshold $a\ge0$, a gap $\eta>0$, a boundary $\beta>0$ and a cap $N$, put
--   $$S_n=\eta\sum_{t=1}^n(X_t-a)-n\eta^2/2,\qquad T=\inf\{n\ge1 : S_n\ge\beta\}.$$
--   The test passes if $T\le N$ and otherwise fails after $N$ samples.
--   1. If $\mu\le a$, the pass probability is at most $e^{-\beta}$.
--   2. If $\mu\ge a+\eta$, $\epsilon>0$ and $N\eta^2\ge\max\{4\beta,32\ln(1/\epsilon)\}$, failure has probability at most $\epsilon$.
--   3. If $\mu\ge a+\eta$, then $\mathbb E\min\{T,N\}\le2(\beta+\eta)/\eta^2$ for every $N$.
--   4. The fixed-sample rule, which takes exactly $N$ samples and passes iff $S_N\ge\beta$, satisfies the bounds of 1 and 2.
--
--   **Formalization Note** The variables live on an arbitrary probability space; $T$ is valued in $\mathbb N\cup\{\infty\}$ and the expectation is in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: $X_1,X_2,\dots$ and $\sum_{t=1}^n$ → $X_0,X_1,\dots$ and the sum of the first $n$; reason: 0-based indexing
--   - encoding: independent $X_t\in[-1,1]$ → mutually independent measurable variables, almost surely in $[-1,1]$; reason: Lean convention
--   - encoding: $\epsilon$ → any $\epsilon>0$; reason: the source needs $\ln(1/\epsilon)$ defined
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §A.1 and Lemma A.1, p.21

import Mathlib
import Definitions.Def_MetricMinTest_oneStreamStat
import Definitions.Def_MetricMinTest_oneStreamTime

namespace MetricMinTest

open MeasureTheory ProbabilityTheory

/-- **Lemma A.1 (One-stream bounds).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §A.1 and Lemma A.1, p.21:
"For independent X_t ∈ [−1, 1] of mean µ, threshold a ≥ 0, gap η > 0, boundary β > 0, and cap N,
put S_n = η ∑_{t=1}^n (X_t − a) − nη²/2, T = inf{n ≥ 1 : S_n ≥ β}. The test passes if T ≤ N and
otherwise fails after N samples. Lemma A.1 (One-stream bounds). If µ ≤ a, the pass probability is
at most e^{−β}. If µ ≥ a + η and Nη² ≥ max{4β, 32 ln(1/ϵ)}, failure has probability at most ϵ.
If µ ≥ a + η, then E min{T, N} ≤ 2(β + η)/η² for every N. The fixed-sample rule, which takes
exactly N samples and passes if and only if S_N ≥ β, satisfies the same two error bounds."

**Formalization Note.** `X : ℕ → Ω → ℝ` (0-based) on a probability space, mutually independent
(`iIndepFun`), each a.s. in `[−1, 1]` with mean `µ`; identical laws are not required. `T` is
`oneStreamTime` (in `ℕ∞`). The cap `N` is any natural number and `ϵ > 0`. Probabilities are of the
events `{T ≤ N}`, `{T > N}`, `{S_N ≥ β}`, `{S_N < β}`; the expectation is an `ℝ≥0∞` integral. -/
theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] (μP : Measure Ω) [IsProbabilityMeasure μP]
    (X : ℕ → Ω → ℝ) (hXm : ∀ t, Measurable (X t)) (hind : iIndepFun X μP)
    (hX : ∀ t, ∀ᵐ ω ∂μP, X t ω ∈ Set.Icc (-1 : ℝ) 1) (mu : ℝ) (hmean : ∀ t, ∫ ω, X t ω ∂μP = mu)
    (a η β : ℝ) (ha : 0 ≤ a) (hη : 0 < η) (hβ : 0 < β) :
    (mu ≤ a → ∀ N : ℕ,
      μP {ω | oneStreamTime η a β (fun t => X t ω) ≤ N} ≤ ENNReal.ofReal (Real.exp (-β))) ∧
    (a + η ≤ mu → ∀ (N : ℕ) (ε : ℝ), 0 < ε → max (4 * β) (32 * Real.log (1 / ε)) ≤ N * η ^ 2 →
      μP {ω | (N : ℕ∞) < oneStreamTime η a β (fun t => X t ω)} ≤ ENNReal.ofReal ε) ∧
    (a + η ≤ mu → ∀ N : ℕ,
      ∫⁻ ω, ((min (oneStreamTime η a β (fun t => X t ω)) (N : ℕ∞) : ℕ∞) : ENNReal) ∂μP ≤
        ENNReal.ofReal (2 * (β + η) / η ^ 2)) ∧
    (mu ≤ a → ∀ N : ℕ,
      μP {ω | β ≤ oneStreamStat η a (fun t => X t ω) N} ≤ ENNReal.ofReal (Real.exp (-β))) ∧
    (a + η ≤ mu → ∀ (N : ℕ) (ε : ℝ), 0 < ε → max (4 * β) (32 * Real.log (1 / ε)) ≤ N * η ^ 2 →
      μP {ω | oneStreamStat η a (fun t => X t ω) N < β} ≤ ENNReal.ofReal ε) := by sorry

end MetricMinTest
