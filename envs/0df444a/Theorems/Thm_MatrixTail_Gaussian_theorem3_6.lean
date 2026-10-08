-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_theorem3_6
-- name    : MatrixTail.Gaussian.theorem3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:50.157298+00:00
-- url     : https://prove2.me/theorems/63648939-03a6-4716-977b-85af7cb3722a
-- title:
--   Theorem 3.6 — master tail bound: P{λmax(Σ X_k) ≥ t} ≤ e^{−θt}·tr exp(Σ log E e^{θX_k})
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices, $d\ge 1$. Then for every $t\in\mathbb R$,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\} \le \inf_{\theta>0}\Big\{ e^{-\theta t}\cdot \operatorname{tr}\exp\Big(\sum_k \log \mathbb E\, e^{\theta X_k}\Big)\Big\}.$$
--
--   This is the master inequality of the paper: it reduces the tail of the largest eigenvalue of an independent sum to the sum of the matrix cumulant generating functions $\log\mathbb E e^{\theta X_k}$. All the specific bounds (Gaussian series, Chernoff, Bernstein) are obtained by bounding these cumulants.
--
--   **Formalization Note** The infimum is stated pointwise: the bound is asserted for every $\theta>0$ for which every entry of each $e^{\theta X_k}$ is integrable. Since an inequality $p\le\inf_\theta F(\theta)$ is equivalent to $p\le F(\theta)$ for all $\theta$, and the paper treats a non-existent mgf as $+\infty$, this is exactly the paper's statement.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Theorem 3.6, display (3.5)

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Theorem 3.6** (Master Tail Bound for Independent Sums), Tropp, arXiv:1004.4389v7, p. 12, display (3.5).
For a finite sequence `X₀, …, X_{n-1}` of independent, random, self-adjoint `d × d` matrices and every
`t ∈ ℝ`,
`P{λmax(Σ_k X_k) ≥ t} ≤ inf_{θ>0} e^{−θt} · tr exp(Σ_k log E e^{θX_k})`.

Formalization Note.
* Matrices are complex (§2.1, p. 7); "self-adjoint" is `IsHermitian`; `[NeZero d]` (the paper's matrices
  have dimension `d ≥ 1`; at `d = 0` the bound fails at `t ≤ 0`).
* `exp` and `log` of matrices are Mathlib's `cfc`; `E` is the entrywise expectation `mean`.
* The infimum is stated pointwise: the bound holds for **every** `θ > 0` at which each mgf `E e^{θX_k}`
  exists (entrywise integrability, the §2.2 regularity made explicit). Since `P ≤ inf_θ F(θ)` iff
  `P ≤ F(θ)` for every `θ`, and the paper takes `F(θ) = +∞` when an mgf does not exist (p. 9), this is
  exactly (3.5).
* Restated locally from mission I of this series (drafts cannot import drafts). -/
theorem theorem3_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hXmeas : ∀ k, Measurable (X k)) (hXherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P) :
    ∀ (t θ : ℝ), 0 < θ → (∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω))) →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
        Real.exp (-θ * t) * MatrixTail.Master.trExp (∑ k, MatrixTail.Master.mlog (MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω)))) := by sorry

end MatrixTail.Gaussian
