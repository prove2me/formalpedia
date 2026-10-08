-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_mixture_value_ge
-- name    : MomentDRO.WorstCov.mixture_value_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:38:04.989988+00:00
-- url     : https://prove2.me/theorems/2e05d43e-520b-4b32-a6d8-497462003a6c
-- title:
--   §5.2, proof of Proposition 3, pp. 20–21 — E[max_l −a_l xᵀξ* − b_l] ≥ Σ_k (−a_k xᵀλ_k − b_k ν_k)
-- statement:
--   Let $K\ge1$, $a,b\in\mathbb R^K$, $x,\hat\mu\in\mathbb R^n$, $\hat\Sigma\succ0$, $\gamma_2>0$, let $\{(\Lambda_k,\lambda_k,\nu_k)\}_{k=1}^K$ be feasible for (19) with every $\nu_k>0$, and let $P_1,\dots,P_K$ be distributions with finite second moments, $\mathbb E_{P_k}[\zeta]=\lambda_k/\nu_k$ and $\mathbb E_{P_k}[\zeta\zeta^{\mathsf T}]=\Lambda_k/\nu_k$. Then the mixture $P^*=\sum_k\nu_kP_k$ satisfies
--   $$\sum_{k=1}^K\big(-a_k\,x^{\mathsf T}\lambda_k-b_k\nu_k\big)\ \le\ \mathbb E_{P^*}\Big[\max_{l}\ -a_l\,x^{\mathsf T}\xi-b_l\Big].$$
--
--   Combined with the bound of (18) by (19), this shows that the mixture built from an optimal solution of (19) attains the maximum of (18).
--
--   **Formalization Note** The objective is written with the sign of the page's displayed computation (p. 21), which is also the sign used throughout this mission.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), pp. 20–21, §5.2, proof of Proposition 3, last display

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem mixture_value_ge {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2)
    (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ)
    (hfeas : Feasible19 μhat Sighat γ2 Lam lam nu)
    (hpos : ∀ k, 0 < nu k)
    (Pk : Fin K → Measure (Fin n → ℝ)) (hPk : ∀ k, MomentDRO.Conf.HasSecondMoments (Pk k))
    (hmean : ∀ k, MomentDRO.Conf.meanVec (Pk k) = (nu k)⁻¹ • lam k)
    (hsecond : ∀ k, MomentDRO.Conf.secondMomentAbout (Pk k) 0 = (nu k)⁻¹ • Lam k) :
    obj19 a b x lam nu ≤ ∫ ξ, pwCost a b x ξ ∂(mixture nu Pk) := by sorry

end MomentDRO.WorstCov
