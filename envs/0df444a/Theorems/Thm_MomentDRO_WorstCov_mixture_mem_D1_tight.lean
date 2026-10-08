-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_mixture_mem_D1_tight
-- name    : MomentDRO.WorstCov.mixture_mem_D1_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:37:38.033286+00:00
-- url     : https://prove2.me/theorems/fcd30d7c-f7a9-4250-afe0-ccc10c9be343
-- title:
--   §5.2, proof of Proposition 3, p. 20 — the law of ξ* = ζ_k̃ lies in D₁(ℝⁿ, µ̂, Σ̂, 0, γ₂) and has largest covariance
-- statement:
--   Let $K\ge1$, $\hat\mu\in\mathbb R^n$, $\hat\Sigma\succ0$, $\gamma_2>0$, and let $\{(\Lambda_k,\lambda_k,\nu_k)\}_{k=1}^K$ be feasible for (19) with (19b) tight,
--   $$\sum_k\Lambda_k=\gamma_2\hat\Sigma+\hat\mu\hat\mu^{\mathsf T},$$
--   and with $\nu_k>0$ for every $k$. Let $P_1,\dots,P_K$ be distributions on $\mathbb R^n$ with finite second moments such that $\mathbb E_{P_k}[\zeta]=\lambda_k/\nu_k$ and $\mathbb E_{P_k}[\zeta\zeta^{\mathsf T}]=\Lambda_k/\nu_k$. Then the mixture $P^*=\sum_k\nu_kP_k$, which is the law of $\xi^*=\zeta_{\tilde k}$ for an independent index $\tilde k$ with $\mathbb P(\tilde k=k)=\nu_k$, satisfies
--   $$P^*\in\mathcal D_1(\mathbb R^n,\hat\mu,\hat\Sigma,0,\gamma_2)\qquad\text{and}\qquad \mathbb E_{P^*}\big[(\xi-\hat\mu)(\xi-\hat\mu)^{\mathsf T}\big]=\gamma_2\hat\Sigma .$$
--
--   So the constructed distribution meets the covariance constraint (1b) with equality: it has the largest covariance the set allows.
--
--   **Formalization Note** The hypothesis $\nu_k>0$ is the page's "assuming without loss of generality that all $\nu_k>0$". The mixture is the measure-level form of $\xi^*=\zeta_{\tilde k}$.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 20, §5.2, proof of Proposition 3, construction of ξ* = ζ_k̃ and the displays for E[ξ*], E[ξ*ξ*ᵀ]

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem mixture_mem_D1_tight {n K : ℕ} [NeZero K]
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2)
    (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ)
    (hfeas : Feasible19 μhat Sighat γ2 Lam lam nu)
    (htight : ∑ k, Lam k = γ2 • Sighat + Matrix.vecMulVec μhat μhat)
    (hpos : ∀ k, 0 < nu k)
    (Pk : Fin K → Measure (Fin n → ℝ)) (hPk : ∀ k, MomentDRO.Conf.HasSecondMoments (Pk k))
    (hmean : ∀ k, MomentDRO.Conf.meanVec (Pk k) = (nu k)⁻¹ • lam k)
    (hsecond : ∀ k, MomentDRO.Conf.secondMomentAbout (Pk k) 0 = (nu k)⁻¹ • Lam k) :
    mixture nu Pk ∈ D1 Set.univ μhat Sighat 0 γ2 ∧
      MomentDRO.Conf.secondMomentAbout (mixture nu Pk) μhat = γ2 • Sighat := by sorry

end MomentDRO.WorstCov
