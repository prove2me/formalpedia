-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_theorem3_6
-- name    : MatrixTail.Bernstein.theorem3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:18.21613+00:00
-- url     : https://prove2.me/theorems/01c3718a-49c9-4488-bef2-07a9b5bcf85c
-- title:
--   Theorem 3.6 — master tail bound: P{λmax(Σ X_k) ≥ t} ≤ e^{−θt} · tr exp(Σ_k log E e^{θX_k})
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices, $d\ge1$. For every $t\in\mathbb R$ and every $\theta>0$ at which the matrix moment generating functions $\mathbb E\,e^{\theta X_k}$ exist,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\}\le e^{-\theta t}\cdot\operatorname{tr}\exp\Big(\sum_k\log\mathbb E\,e^{\theta X_k}\Big).$$
--
--   Taking the infimum over $\theta>0$ gives the paper's display (3.5). This is the master inequality from which every tail bound of the paper is derived: it controls the largest eigenvalue of an independent sum by the sum of the matrix cumulant generating functions $\log\mathbb E\,e^{\theta X_k}$.
--
--   **Formalization Note** The infimum over $\theta$ is stated for each admissible $\theta$, which is equivalent: the paper treats a non-existent mgf as $+\infty$. Existence of $\mathbb E\,e^{\theta X_k}$ is the integrability of its entries. This result is the goal of the first mission of the series and is restated here as a milestone.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Theorem 3.6, display (3.5)

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- **Theorem 3.6** (Master Tail Bound for Independent Sums), Tropp, arXiv:1004.4389v7, p. 12, display (3.5).
Let `X_1, …, X_n` (indexed by `Fin n`) be independent random self-adjoint `d × d` complex matrices. For every `t ∈ ℝ` and every
`θ > 0` at which the matrix mgfs `E e^{θ X_k}` exist,
`P{λmax(Σ_k X_k) ≥ t} ≤ e^{−θt} · tr exp(Σ_k log E e^{θ X_k})`.

Formalization Note: matrices are complex (§2.1); `exp`/`log` are the continuous functional calculus `cfc`; the
expectation of a random matrix is entrywise. The paper's `inf_{θ>0}` is stated pointwise in `θ` (an inequality
`P ≤ inf_θ F(θ)` is equivalent to `P ≤ F(θ)` for every `θ`); the paper admits non-existent mgfs as `+∞`, so
the integrability hypothesis on `e^{θ X_k}` (the §2.2 regularity) excludes only trivial bounds. `[NeZero d]`
encodes "dimension `d ≥ 1`": for `d = 0` the bound is false at `t ≤ 0`. This theorem is restated locally from
mission I, whose goal it is. -/
theorem theorem3_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P) (t θ : ℝ) (hθ : 0 < θ)
    (h_mgf : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω))) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      Real.exp (-θ * t) * MatrixTail.Master.trExp (∑ k, MatrixTail.Master.mlog (MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω)))) := by sorry

end MatrixTail.Bernstein
