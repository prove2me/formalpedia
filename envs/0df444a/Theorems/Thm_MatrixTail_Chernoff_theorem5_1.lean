-- Prove2me | Theorems.Thm_MatrixTail_Chernoff_theorem5_1
-- name    : MatrixTail.Chernoff.theorem5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:18.300645+00:00
-- url     : https://prove2.me/theorems/8e2954e7-0e03-40a7-b8ee-1a6f96509e82
-- title:
--   Theorem 5.1 (Matrix Chernoff I) — eigenvalue tails of an average of psd contractions are bounded by d·e^{−n·D(α‖μ̄)}
-- statement:
--   Let $X_1,\dots,X_n$, $n\ge1$, be independent random Hermitian $d\times d$ complex matrices, $d\ge1$, such that almost surely
--   $$X_k\succcurlyeq 0\quad\text{and}\quad \lambda_{\max}(X_k)\le 1 .$$
--   Let the extreme eigenvalues of the average expectation be
--   $$\bar\mu_{\min} := \lambda_{\min}\Big(\frac1n\sum_{k=1}^n\mathbb E X_k\Big),\qquad \bar\mu_{\max} := \lambda_{\max}\Big(\frac1n\sum_{k=1}^n\mathbb E X_k\Big),$$
--   and let $\mathrm D(a\,\|\,u) = a(\log a-\log u)+(1-a)(\log(1-a)-\log(1-u))$ be the binary information divergence. Then
--
--   1. for every $0\le\alpha\le\bar\mu_{\min}$,
--   $$\mathbb P\Big\{\lambda_{\min}\Big(\frac1n\sum_{k=1}^n X_k\Big)\le\alpha\Big\}\le d\cdot e^{-n\,\mathrm D(\alpha\,\|\,\bar\mu_{\min})};$$
--   2. for every $\bar\mu_{\max}\le\alpha\le1$,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\frac1n\sum_{k=1}^n X_k\Big)\ge\alpha\Big\}\le d\cdot e^{-n\,\mathrm D(\alpha\,\|\,\bar\mu_{\max})}.$$
--
--   This is the matrix analogue of the strongest form of the scalar Chernoff inequality for the proportion of successes in independent Bernoulli trials; the price of the matrix setting is only the dimensional factor $d$.
--
--   **Formalization Note** $d$, which the theorem does not name, is the dimension of the matrices. The two bounds are a conjunction, each with the paper's range of $\alpha$. In Lean $\log0=0$, so at the boundary cases where the true divergence is $+\infty$ the stated bound is weaker than the paper's, never stronger. Integrability of $X_k$ is implied by boundedness.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 20, Theorem 5.1

import Mathlib
import Definitions.Def_MatrixTail_Chernoff_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- **Theorem 5.1 (Matrix Chernoff I)** (Tropp, arXiv:1004.4389v7, p. 20). Consider a sequence
`X_1, …, X_n` of independent, random, self-adjoint matrices that satisfy `X_k ≽ 0` and `λmax(X_k) ≤ 1`
almost surely. Compute the minimum and maximum eigenvalues of the average expectation,
`μ̄min := λmin((1/n) Σ_k E X_k)` and `μ̄max := λmax((1/n) Σ_k E X_k)`. Then
`P{λmin((1/n) Σ_k X_k) ≤ α} ≤ d · e^{−n·D(α ‖ μ̄min)}` for `0 ≤ α ≤ μ̄min`, and
`P{λmax((1/n) Σ_k X_k) ≥ α} ≤ d · e^{−n·D(α ‖ μ̄max)}` for `μ̄max ≤ α ≤ 1`,
with `D` the binary information divergence `binDiv`.

Formalization Note: the page does not say what `d` is; it is the dimension of the matrices (§2.1;
Corollary 5.2's proof and §1.2), so `X_k : Ω → Matrix (Fin d) (Fin d) ℂ` with `[NeZero d]`. Matrices are
complex, `E` is the entrywise expectation. "`X_k ≽ 0`" and "`λmax(X_k) ≤ 1`" hold almost surely, as the
page says; self-adjointness holds for every outcome. `0 < n` because of the averages `1/n` (at `n = 0`
Lean's `1/0 = 0` would make both averages `0`). Integrability of `X_k` follows from boundedness and is not
assumed. The two bounds are stated as a conjunction; each carries the paper's range of `α`. At the boundary
cases where the true divergence is `+∞` (`μ̄min = 1`, or `μ̄max = 0` with `α > 0`), Lean's finite value of
`binDiv` only makes the right-hand side larger. -/
theorem theorem5_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (hn : 0 < n) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P)
    (hpsd : ∀ k, ∀ᵐ ω ∂P, (X k ω).PosSemidef) (hle : ∀ k, ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X k ω) ≤ 1) :
    (∀ α : ℝ, 0 ≤ α → α ≤ lambdaMin ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (X k)) →
      P.real {ω | lambdaMin ((1 / n : ℝ) • ∑ k, X k ω) ≤ α} ≤
        d * Real.exp (-(n : ℝ) * binDiv α (lambdaMin ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (X k))))) ∧
    (∀ α : ℝ, MatrixTail.Master.lambdaMax ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (X k)) ≤ α → α ≤ 1 →
      P.real {ω | α ≤ MatrixTail.Master.lambdaMax ((1 / n : ℝ) • ∑ k, X k ω)} ≤
        d * Real.exp (-(n : ℝ) * binDiv α (MatrixTail.Master.lambdaMax ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (X k))))) := by sorry

end MatrixTail.Chernoff
