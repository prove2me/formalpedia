-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_proposition_3
-- name    : MomentDRO.WorstCov.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:38:02.322995+00:00
-- url     : https://prove2.me/theorems/36af8a60-57df-4701-8fe5-2afb1f1c3950
-- title:
--   Proposition 3, p. 19 — for piecewise-linear concave utility and support ℝⁿ, a worst-case distribution over D₁(ℝⁿ, µ̂, Σ̂, γ₁, γ₂) has E[(ξ−µ̂)(ξ−µ̂)ᵀ] = γ₂Σ̂
-- statement:
--   Let $n\ge0$ assets have random return vector $\xi\in\mathbb R^n$ and let $x\in\mathbb R^n$ be a portfolio. Let the utility be piecewise linear concave, $u(y)=\min_{k\in\{1,\dots,K\}}a_ky+b_k$ with $K\ge1$, so that the cost is $h(x,\xi)=\max_k(-a_k\,\xi^{\mathsf T}x-b_k)=-u(\xi^{\mathsf T}x)$. Let $\hat\mu\in\mathbb R^n$, $\hat\Sigma\succ0$, $\gamma_1\ge0$ and $\gamma_2>0$, and consider the inner problem of the robust portfolio problem (16) with unconstrained support,
--   $$\max_{f_\xi\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,\gamma_1,\gamma_2)}\ \mathbb E_\xi\big[\max_k -a_k\,\xi^{\mathsf T}x-b_k\big].$$
--   Then (18) attains its maximum at a distribution whose covariance constraint is tight: there is $P^*\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,\gamma_1,\gamma_2)$ with
--   $$\mathbb E_{P^*}\big[(\xi-\hat\mu)(\xi-\hat\mu)^{\mathsf T}\big]=\gamma_2\hat\Sigma\qquad\text{and}\qquad \mathbb E_{Q}[h(x,\xi)]\le\mathbb E_{P^*}[h(x,\xi)]\ \ \text{for every }Q\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,\gamma_1,\gamma_2).$$
--
--   That is, the covariance constraint (1b), $\mathbb E[(\xi-\hat\mu)(\xi-\hat\mu)^{\mathsf T}]\preceq\gamma_2\hat\Sigma$, holds with equality at a worst-case distribution (for $\gamma_1=0$ the mean is $\hat\mu$ and this matrix is the covariance of $P^*$): the worst-case distribution has the largest covariance the set allows, and a lower bound on the covariance would not change the robust portfolio problem.
--
--   **Formalization Note** The proposition is worded for "the robust portfolio optimization problem", i.e. problem (16) with $\mathcal D_1(\mathcal S_\xi,\hat\mu,\hat\Sigma,\gamma_1,\gamma_2)$ (§5.1, Theorem 4); its proof writes out only the case $\gamma_1=0$ ("for simplicity of our derivations", the inner problem (18)). The statement covers every $\gamma_1\ge0$, as the proposition does; $\gamma_1\ge0$ is Assumption 3's. "Infinite support constraint" is $S=\mathbb R^n$. The portfolio $x$ ranges over all of $\mathbb R^n$: the simplex constraint (16b) is not used by the inner problem, so dropping it makes the statement stronger. $\hat\Sigma\succ0$ is Assumption 3's $\Sigma_0\succ0$ (also endnote 1, p. 22); $\gamma_2>0$ is §3's. The conclusion asserts that one maximizer is tight, not that every maximizer is (for $K=1$ every member of $\mathcal D_1$ is a maximizer).
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 19, §5.2, Proposition 3 and (18); proof on pp. 19–21

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem proposition_3 {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ1 γ2 : ℝ) (hγ1 : 0 ≤ γ1) (hγ2 : 0 < γ2) :
    ∃ P ∈ D1 Set.univ μhat Sighat γ1 γ2,
      MomentDRO.Conf.secondMomentAbout P μhat = γ2 • Sighat ∧
        ∀ Q ∈ D1 Set.univ μhat Sighat γ1 γ2,
          ∫ ξ, pwCost a b x ξ ∂Q ≤ ∫ ξ, pwCost a b x ξ ∂P := by sorry

end MomentDRO.WorstCov
