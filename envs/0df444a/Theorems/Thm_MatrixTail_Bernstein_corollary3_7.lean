-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_corollary3_7
-- name    : MatrixTail.Bernstein.corollary3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:26.647983+00:00
-- url     : https://prove2.me/theorems/0d5e18eb-bf40-4f56-913e-2ad117d0ac37
-- title:
--   Corollary 3.7 — if E e^{θX_k} ≼ e^{g(θ)A_k}, then P{λmax(Σ X_k) ≥ t} ≤ d · e^{−θt + g(θ)ρ}, ρ = λmax(Σ A_k)
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices, $d\ge1$, and let $A_1,\dots,A_n$ be fixed self-adjoint matrices. Put $\rho:=\lambda_{\max}\big(\sum_k A_k\big)$. Fix $\theta>0$ and a number $g(\theta)\ge0$ such that the mgfs $\mathbb E\,e^{\theta X_k}$ exist and
--   $$\mathbb E\,e^{\theta X_k}\preccurlyeq e^{g(\theta)\,A_k}\qquad\text{for every }k .$$
--   Then for every $t\in\mathbb R$,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\}\le d\cdot e^{-\theta t+g(\theta)\,\rho}.$$
--
--   Taking the infimum over $\theta>0$ gives the paper's (3.7). The corollary turns a semidefinite bound on each matrix mgf into a scalar tail bound with the dimensional factor $d$; the matrix Bernstein inequalities follow from it once the mgf bound is known.
--
--   **Formalization Note** The paper's function $g:(0,\infty)\to[0,\infty]$ is used one value at a time: for each $\theta$, $g(\theta)$ is a nonnegative real number, and values $g(\theta)=+\infty$ give only the trivial bound. This is equivalent to the paper's statement. The semidefinite order $\preccurlyeq$ is Mathlib's Loewner order. The result is also a milestone of the second mission of the series.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Corollary 3.7, displays (3.6)–(3.7)

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- **Corollary 3.7**, Tropp, arXiv:1004.4389v7, p. 12, displays (3.6)–(3.7).
Let `X_1, …, X_n` (indexed by `Fin n`) be independent random self-adjoint `d × d` complex matrices and `A_1, …, A_n` fixed
self-adjoint matrices. If, at some `θ > 0` and with `γ = g(θ) ≥ 0`, `E e^{θ X_k} ≼ e^{γ A_k}` for every `k`
(3.6), then for every `t ∈ ℝ`, `P{λmax(Σ_k X_k) ≥ t} ≤ d · e^{−θt + γ ρ}` with `ρ = λmax(Σ_k A_k)` (3.7).

Formalization Note: the paper's `g : (0,∞) → [0,∞]` and `inf_{θ>0}` are stated pointwise: for each `θ > 0` the
value `γ = g(θ) ∈ [0,∞)` is a free nonnegative real, and `θ` with `g(θ) = ∞` contribute only the trivial bound
`+∞`. This pointwise form is equivalent to the paper's (and implies the special case of a real-valued `g`
assumed for all `θ > 0`). Integrability of the entries of `e^{θ X_k}` is the §2.2 regularity. `≼` is
Mathlib's Loewner order (`MatrixOrder`). `[NeZero d]`: dimension `d ≥ 1`. Restated locally from mission II. -/
theorem corollary3_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P)
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA_herm : ∀ k, (A k).IsHermitian)
    (t θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 ≤ γ)
    (h_mgf : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => MatrixTail.Master.mexp (θ • X k ω)))
    (h_bound : ∀ k, MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X k ω)) ≤ MatrixTail.Master.mexp (γ • A k)) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      (d : ℝ) * Real.exp (-θ * t + γ * MatrixTail.Master.lambdaMax (∑ k, A k)) := by sorry

end MatrixTail.Bernstein
