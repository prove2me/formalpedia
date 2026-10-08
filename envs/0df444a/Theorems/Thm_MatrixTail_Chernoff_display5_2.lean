-- Prove2me | Theorems.Thm_MatrixTail_Chernoff_display5_2
-- name    : MatrixTail.Chernoff.display5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:51.502979+00:00
-- url     : https://prove2.me/theorems/6748859b-1bf2-44fd-817c-8ddfc712e78a
-- title:
--   Display (5.2) — P{λmin(Σ X_k) ≤ t} ≤ d·exp(θt + n·log(1 − (1 − e^{−θ})·μ̄min))
-- statement:
--   Let $X_1,\dots,X_n$, $n\ge1$, be independent random Hermitian $d\times d$ complex matrices, $d\ge1$, such that almost surely $X_k\succcurlyeq 0$ and $\lambda_{\max}(X_k)\le 1$. Let
--   $$\bar\mu_{\min} := \lambda_{\min}\Big(\frac1n\sum_{k=1}^n \mathbb E X_k\Big).$$
--   Then for every $t\in\mathbb R$ and every $\theta>0$,
--   $$\mathbb P\Big\{\lambda_{\min}\Big(\sum_{k} X_k\Big)\le t\Big\} \le d\cdot \exp\big(\theta t + n\cdot\log\big(1-(1-e^{-\theta})\,\bar\mu_{\min}\big)\big).$$
--
--   This is the lower-tail estimate in the proof of Theorem 5.1, obtained by applying Corollary 3.9 to the sequence $\{-X_k\}$ together with Lemma 5.8. It leads to the lower divergence bound of Theorem 5.1 and to the lower bound of Corollary 5.2.
--
--   **Formalization Note** "Positive semidefinite" and "$\lambda_{\max}\le1$" hold almost surely; integrability is implied. Since $0\le\bar\mu_{\min}\le1$ and $0<1-e^{-\theta}<1$, the logarithm's argument is at least $e^{-\theta}>0$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 23, Theorem 5.1, proof of the lower bound, display (5.2)

import Mathlib
import Definitions.Def_MatrixTail_Chernoff_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- **Display (5.2)** (Tropp, arXiv:1004.4389v7, Theorem 5.1, proof of the lower bound, p. 23). Under
the hypotheses of Theorem 5.1 (independent random self-adjoint `X_k ≽ 0` with `λmax(X_k) ≤ 1` almost
surely, `k = 1, …, n`), with `μ̄min = λmin((1/n) Σ_k E X_k)` and `g(θ) := 1 − e^{−θ}` for `θ > 0`,
`P{λmin(Σ_k X_k) ≤ t} = P{λmax(Σ_k (−X_k)) ≥ −t}
  ≤ d · exp(θt + n · log λmax((1/n) Σ_k (I − g(θ) · E X_k)))
  = d · exp(θt + n · log(1 − g(θ) · λmin((1/n) Σ_k E X_k)))
  = d · exp(θt + n · log(1 − g(θ) · μ̄min))`.
The milestone is the outer inequality: the probability is at most the last line, for every `t` and `θ > 0`.

Formalization Note: complex matrices, entrywise expectation; "psd" and "`λmax ≤ 1`" hold almost surely,
self-adjointness for every outcome. `0 < n`, `[NeZero d]`. The argument of the log is at least `e^{−θ} > 0`
because `0 ≤ μ̄min ≤ 1` (implied by the hypotheses) and `0 < g(θ) < 1`. Integrability of `X_k` follows from
boundedness and is not assumed. -/
theorem display5_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (hn : 0 < n) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P)
    (hpsd : ∀ k, ∀ᵐ ω ∂P, (X k ω).PosSemidef) (hle : ∀ k, ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X k ω) ≤ 1)
    (t θ : ℝ) (hθ : 0 < θ) :
    P.real {ω | lambdaMin (∑ k, X k ω) ≤ t} ≤
      d * Real.exp (θ * t + n * Real.log
        (1 - (1 - Real.exp (-θ)) * lambdaMin ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (X k)))) := by sorry

end MatrixTail.Chernoff
