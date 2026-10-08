-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_optimal_values_eq
-- name    : MomentDRO.WorstCov.optimal_values_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:37:47.57966+00:00
-- url     : https://prove2.me/theorems/26bf4c76-54e3-44df-96b2-a2b6b4613e26
-- title:
--   §5.2, proof of Proposition 3, p. 19 — the SDP (19) and the inner problem (18) have the same optimal value
-- statement:
--   Let $K\ge1$, $a,b\in\mathbb R^K$, $x,\hat\mu\in\mathbb R^n$, $\hat\Sigma\succ0$ and $\gamma_2>0$. For every real $v$, $v$ is the maximum (attained) of the SDP
--   $$\max\Big\{\textstyle\sum_k -a_k\,x^{\mathsf T}\lambda_k-b_k\nu_k\ :\ \{(\Lambda_k,\lambda_k,\nu_k)\}_{k=1}^K\ \text{feasible for (19b)–(19d)}\Big\}$$
--   if and only if $v$ is the maximum (attained) of the inner problem
--   $$\max_{Q\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,0,\gamma_2)}\ \mathbb E_Q\big[\max_k -a_k\,\xi^{\mathsf T}x-b_k\big].\tag{18}$$
--
--   This is the page's claim that (19) "by strong duality achieves the same optimum" as (18), stated as an equality of attained maxima.
--
--   **Formalization Note** "$v$ is the maximum" is `IsGreatest`, never a real supremum. $\gamma_1=0$, $S=\mathbb R^n$.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 19, §5.2, proof of Proposition 3, (18) and (19)

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem optimal_values_eq {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) (v : ℝ) :
    IsGreatest {t | ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ)
        (nu : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam lam nu ∧ t = obj19 a b x lam nu} v ↔
      IsGreatest ((fun Q => ∫ ξ, pwCost a b x ξ ∂Q) '' D1 Set.univ μhat Sighat 0 γ2) v := by sorry

end MomentDRO.WorstCov
