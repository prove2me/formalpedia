-- Prove2me | Theorems.Thm_MatrixTail_Chernoff_theorem3_6
-- name    : MatrixTail.Chernoff.theorem3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:56.378976+00:00
-- url     : https://prove2.me/theorems/9093d9d1-79bc-4c30-969c-25de0eb5e7d6
-- title:
--   Theorem 3.6 — master tail bound: P{λmax(Σ X_k) ≥ t} ≤ e^{−θt}·tr exp(Σ_k log E e^{θX_k})
-- statement:
--   Let $X_1,\dots,X_n$ be independent random Hermitian $d\times d$ complex matrices, $d\ge1$, on a probability space. Fix $t\in\mathbb R$ and $\theta>0$ such that every matrix moment generating function $\mathbb E\,e^{\theta X_k}$ exists (its entries are integrable). Then
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_{k} X_k\Big)\ge t\Big\} \le e^{-\theta t}\cdot \operatorname{tr}\exp\Big(\sum_{k}\log \mathbb E\,e^{\theta X_k}\Big).$$
--   Taking the infimum over $\theta>0$ gives the paper's bound (3.5).
--
--   This is the master inequality from which every tail bound of the paper is derived: it reduces the tail of the largest eigenvalue of an independent sum to the matrix cumulant generating functions $\log\mathbb E\,e^{\theta X_k}$ of the summands.
--
--   **Formalization Note** The infimum over $\theta>0$ is stated as a bound for every $\theta>0$ at which the mgfs exist; the paper counts a nonexistent mgf as $+\infty$, so this is exactly the infimum. Expectations are entrywise; $\exp$ and $\log$ are the spectral (`cfc`) functions. This restates the goal of mission I of the series.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Theorem 3.6, (3.5)

import Mathlib
import Definitions.Def_MatrixTail_Chernoff_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- **Theorem 3.6 (Master Tail Bound for Independent Sums)** (Tropp, arXiv:1004.4389v7, p. 12, (3.5)).
Consider a finite sequence `X_1, …, X_n` of independent, random, self-adjoint `d × d` matrices. For all
`t ∈ ℝ`,
`P{λmax(Σ_k X_k) ≥ t} ≤ inf_{θ>0} e^{−θt} · tr exp(Σ_k log E e^{θX_k})`.

Formalization Note: matrices are complex (§2.1); `exp` and `log` are Mathlib's `cfc`; `E` is the
entrywise expectation `mean`. The infimum is read as "for every `θ > 0` at which the matrix mgfs exist":
the bound is stated for every such `θ`, with the integrability of the entries of every `e^{θX_k}` as the
§2.2 regularity hypothesis (the paper counts a nonexistent mgf as `+∞`, so this is exactly the infimum).
`[NeZero d]` excludes `0 × 0` matrices, for which `λmax` would be `sSup ∅ = 0`. Restated from mission I
(its goal) because drafts cannot import drafts. -/
theorem theorem3_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P) (t θ : ℝ) (hθ : 0 < θ)
    (hint : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω))) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      Real.exp (-θ * t) * MatrixTail.Master.trExp (∑ k, MatrixTail.Master.mlog (MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω)))) := by sorry

end MatrixTail.Chernoff
