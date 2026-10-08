-- Prove2me | Theorems.Thm_MatrixTail_Chernoff_corollary3_9
-- name    : MatrixTail.Chernoff.corollary3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:13.707343+00:00
-- url     : https://prove2.me/theorems/9e39f1d6-2b80-40e3-bb2c-e0247b035fd4
-- title:
--   Corollary 3.9 — P{λmax(Σ X_k) ≥ t} ≤ d·exp(−θt + n·log λmax((1/n)Σ E e^{θX_k}))
-- statement:
--   Let $X_1,\dots,X_n$, $n\ge1$, be independent random Hermitian $d\times d$ complex matrices, $d\ge1$. Fix $t\in\mathbb R$ and $\theta>0$ such that every $\mathbb E\,e^{\theta X_k}$ exists. Then
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_{k=1}^n X_k\Big)\ge t\Big\} \le d\cdot \exp\Big(-\theta t + n\cdot \log\lambda_{\max}\Big(\frac1n\sum_{k=1}^n \mathbb E\,e^{\theta X_k}\Big)\Big).$$
--   Taking the infimum over $\theta>0$ gives (3.9).
--
--   Compared with the master bound, the matrix mgfs of the summands are combined under a single logarithm and the trace is replaced by the dimensional factor $d$. Both matrix Chernoff inequalities are derived from this form.
--
--   **Formalization Note** The infimum over $\theta$ is read as a bound for every admissible $\theta>0$. The argument of the logarithm is the largest eigenvalue of an average of positive-definite matrices and is therefore positive.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 13, Corollary 3.9, (3.9)

import Mathlib
import Definitions.Def_MatrixTail_Chernoff_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- **Corollary 3.9** (Tropp, arXiv:1004.4389v7, p. 13, (3.9)). Consider a sequence `X_1, …, X_n` of
independent, random, self-adjoint matrices with dimension `d`. For all `t ∈ ℝ`,
`P{λmax(Σ_{k=1}^n X_k) ≥ t} ≤ d · inf_{θ>0} exp(−θt + n · log λmax((1/n) Σ_{k=1}^n E e^{θX_k}))`.

Formalization Note: complex matrices, `cfc` exponential, entrywise expectation. The infimum is read as
"for every `θ > 0` at which the mgfs exist" (integrability of the entries of each `e^{θX_k}`, the §2.2
regularity). `0 < n` because of the average `1/n` (the sequence is indexed `k = 1, …, n`); `[NeZero d]`
because `d` is the dimension. The argument of `Real.log` is the largest eigenvalue of a MatrixTail.Master.mean of
positive-definite matrices, hence positive: no junk value of `log` is used. -/
theorem corollary3_9 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (hn : 0 < n) (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P) (t θ : ℝ) (hθ : 0 < θ)
    (hint : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω))) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      d * Real.exp (-θ * t + n * Real.log
        (MatrixTail.Master.lambdaMax ((1 / n : ℝ) • ∑ k, MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω))))) := by sorry

end MatrixTail.Chernoff
