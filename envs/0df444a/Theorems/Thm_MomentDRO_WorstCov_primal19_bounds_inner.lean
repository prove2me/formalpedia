-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_primal19_bounds_inner
-- name    : MomentDRO.WorstCov.primal19_bounds_inner
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:37:14.154112+00:00
-- url     : https://prove2.me/theorems/7320008c-e644-4c97-b680-69e0c33fd6d8
-- title:
--   §5.2, proof of Proposition 3, p. 19 — the value of the SDP (19) bounds the inner problem (18)
-- statement:
--   Let $n\ge0$ and $K\ge1$, let $a,b\in\mathbb R^K$ define the cost $h(x,\xi)=\max_k(-a_k\xi^{\mathsf T}x-b_k)$, let $x\in\mathbb R^n$, $\hat\mu\in\mathbb R^n$, let $\hat\Sigma\succ0$ and $\gamma_2>0$. For every distribution $Q\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,0,\gamma_2)$ there is a feasible point $\{(\Lambda_k,\lambda_k,\nu_k)\}_{k=1}^K$ of the SDP
--   $$\begin{aligned}&\text{maximize}\ \ \textstyle\sum_{k}-a_k\,x^{\mathsf T}\lambda_k-b_k\nu_k\\ &\text{subject to}\ \ \textstyle\sum_k\Lambda_k\preceq\gamma_2\hat\Sigma+\hat\mu\hat\mu^{\mathsf T},\quad \sum_k\lambda_k=\hat\mu,\quad\sum_k\nu_k=1,\quad\begin{bmatrix}\Lambda_k&\lambda_k\\\lambda_k^{\mathsf T}&\nu_k\end{bmatrix}\succeq0\ \ \forall k,\end{aligned}\tag{19}$$
--   whose objective value is at least the expected cost under $Q$:
--   $$\mathbb E_Q\big[\max_k -a_k\,\xi^{\mathsf T}x-b_k\big]\le\sum_{k=1}^K\big(-a_k\,x^{\mathsf T}\lambda_k-b_k\nu_k\big).$$
--
--   The page states that (19) "by strong duality achieves the same optimum" as (18). This item is the half of that equality used by the proof: every value of (18) is dominated by a value of (19). The other half is the attainment proved through the mixture construction.
--
--   **Formalization Note** $\gamma_1=0$ and $S=\mathbb R^n$ as in (18). The objective is written with the sign of the proof's last display (p. 21), not the misprinted sign of (19a).
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 19, §5.2, proof of Proposition 3, (18) and (19a)–(19d)

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem primal19_bounds_inner {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) :
    ∀ Q ∈ D1 Set.univ μhat Sighat 0 γ2,
      ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ),
        Feasible19 μhat Sighat γ2 Lam lam nu ∧
          ∫ ξ, pwCost a b x ξ ∂Q ≤ obj19 a b x lam nu := by sorry

end MomentDRO.WorstCov
