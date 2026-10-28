-- Prove2me | Theorems.Thm_LambdaVaRAmb_Robust_corollary_1
-- name    : LambdaVaRAmb.Robust.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:41.613981+00:00
-- url     : https://prove2.me/theorems/fe46f1f4-6b62-4783-844b-bfb1dec39288
-- title:
--   Corollary 1 — for Λ ∈ ℋ_I and a class 𝒫 of probabilities, ℚ̄ and ℚ̲ are capacities, sup_{ℚ∈𝒫} ΛVaR^ℚ = ΛVaR^{ℚ̄}, inf_{ℚ∈𝒫} ΛVaR^{+,ℚ} = ΛVaR^{+,ℚ̲}
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space and $\mathcal P$ a nonempty class of probability measures on it. Put $\overline{\mathbb Q}(A)=\sup_{\mathbb Q\in\mathcal P}\mathbb Q(A)$ and $\underline{\mathbb Q}(A)=\inf_{\mathbb Q\in\mathcal P}\mathbb Q(A)$. Then $\overline{\mathbb Q}$ and $\underline{\mathbb Q}$ are capacities, and for every increasing $\Lambda:\mathbb R\to(0,1)$ and every random variable $X$,
--   $$\sup_{\mathbb Q\in\mathcal P}\Lambda\mathrm{VaR}^{\mathbb Q}(X)=\Lambda\mathrm{VaR}^{\overline{\mathbb Q}}(X)\qquad\text{and}\qquad\inf_{\mathbb Q\in\mathcal P}\Lambda\mathrm{VaR}^{+,\mathbb Q}(X)=\Lambda\mathrm{VaR}^{+,\underline{\mathbb Q}}(X).$$
--
--   This is the special case of Proposition 2 for a class of probability measures: the robust $\Lambda$VaR over a set of models is a $\Lambda$VaR with respect to the upper probability. It reduces the robust problems of §4 to computing $\overline{\mathbb Q}$.
--
--   **Formalization Note** The equalities hold in `EReal`. $\mathcal P$ is assumed nonempty (as in Proposition 2), $X$ is measurable, and the envelopes are evaluated through real suprema and infima of values in $[0,1]$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 8, Corollary 1

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Robust

open MeasureTheory

theorem corollary_1 {Ω : Type*} [MeasurableSpace Ω]
    (Pcl : Set (Measure Ω)) (hPcl : Pcl.Nonempty) (hprob : ∀ Q ∈ Pcl, IsProbabilityMeasure Q)
    (Λ : ℝ → ℝ) (hΛ : InHI Λ) :
    IsCapacity (upperProb Pcl) ∧ IsCapacity (lowerProb Pcl) ∧
      ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ Pcl, LVaR Λ (probCap Q) X) = LVaR Λ (upperProb Pcl) X ∧
          (⨅ Q ∈ Pcl, LVaRPlus Λ (probCap Q) X) = LVaRPlus Λ (lowerProb Pcl) X := by sorry

end LambdaVaRAmb.Robust
