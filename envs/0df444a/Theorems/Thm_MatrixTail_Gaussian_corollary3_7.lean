-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_corollary3_7
-- name    : MatrixTail.Gaussian.corollary3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:57.946858+00:00
-- url     : https://prove2.me/theorems/38d9a04d-82d6-4634-90c0-7e58772e16b7
-- title:
--   Corollary 3.7 — if E e^{θX_k} ≼ e^{g(θ)A_k}, then P{λmax(Σ X_k) ≥ t} ≤ d·inf_θ e^{−θt+g(θ)ρ}
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices ($d\ge1$), and let $A_1,\dots,A_n$ be fixed self-adjoint $d\times d$ matrices. Suppose a function $g:(0,\infty)\to[0,\infty]$ satisfies
--   $$\mathbb E\, e^{\theta X_k} \preccurlyeq e^{g(\theta) A_k}\qquad\text{for } \theta>0,$$
--   where $\preccurlyeq$ is the semidefinite order, and put $\rho := \lambda_{\max}\big(\sum_k A_k\big)$. Then for every $t\in\mathbb R$,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\}\le d\cdot\inf_{\theta>0} e^{-\theta t + g(\theta)\rho}.$$
--
--   This turns a semidefinite bound on each summand's mgf into a scalar tail bound, with the scale parameter given by the largest eigenvalue of a sum. The Gaussian, Chernoff and Bernstein inequalities of the paper are all applications of it.
--
--   **Formalization Note** The statement is given pointwise in $\theta$: for each $\theta>0$ and each number $\gamma\ge0$ such that the mgfs exist (entrywise integrability) and $\mathbb E e^{\theta X_k}\preccurlyeq e^{\gamma A_k}$ for all $k$, the probability is at most $d\, e^{-\theta t+\gamma\rho}$. Values $\theta$ with $g(\theta)=+\infty$ contribute only the trivial bound, so this is equivalent to the paper's form.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Corollary 3.7, displays (3.6)–(3.7)

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Corollary 3.7**, Tropp, arXiv:1004.4389v7, p. 12, displays (3.6)–(3.7). Let `X₀, …, X_{n-1}` be
independent, random, self-adjoint `d × d` matrices and `A₀, …, A_{n-1}` fixed self-adjoint `d × d` matrices,
with scale parameter `ρ := λmax(Σ_k A_k)`. If `g : (0,∞) → [0,∞]` satisfies `E e^{θX_k} ≼ e^{g(θ)·A_k}` for
`θ > 0`, then for all `t ∈ ℝ`, `P{λmax(Σ_k X_k) ≥ t} ≤ d · inf_{θ>0} e^{−θt+g(θ)·ρ}`.

Formalization Note.
* Complex Hermitian matrices, `[NeZero d]`, `≼` is Mathlib's Loewner order `≤` under `MatrixOrder`;
  `exp` is `cfc`; `E` is entrywise.
* **Pointwise reading of `g` and of the infimum.** The statement is given for each `θ > 0` and each finite
  value `γ = g(θ) ≥ 0` at which the mgfs exist (entrywise integrability, §2.2) and (3.6) holds; the
  conclusion is the term `d · e^{−θt+γρ}` of the infimum. Since `P ≤ d · inf_θ F(θ)` iff `P ≤ d · F(θ)` for
  every `θ`, and a `θ` with `g(θ) = +∞` contributes only the trivial bound `+∞`, this is equivalent to
  (3.7) for every `g : (0,∞) → [0,∞]`; requiring (3.6) only at the one `θ` used makes it no weaker. -/
theorem corollary3_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hXmeas : ∀ k, Measurable (X k)) (hXherm : ∀ k ω, (X k ω).IsHermitian)
    (hindep : iIndepFun X P)
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hAherm : ∀ k, (A k).IsHermitian) :
    ∀ (t θ γ : ℝ), 0 < θ → 0 ≤ γ →
      (∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω))) →
      (∀ k, MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω)) ≤ MatrixTail.Master.mexp (γ • A k)) →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
        d * Real.exp (-θ * t + γ * MatrixTail.Master.lambdaMax (∑ k, A k)) := by sorry

end MatrixTail.Gaussian
