-- Prove2me | Theorems.Thm_OODLearnable_overlap_breaks_linear_condition
-- name    : OODLearnable.overlap_breaks_linear_condition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:26:54.580741+00:00
-- url     : https://prove2.me/theorems/5c74b98c-93d8-47dc-adc3-3b5140b19751
-- title:
--   Theorem 3: overlap between ID and OOD breaks the linear condition
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, let $\mathcal H$ be a hypothesis space and let $\mathscr D$ be a priori-unknown space. Suppose some $D_{XY}\in\mathscr D$ has overlap between ID and OOD (Definition 4) and satisfies
--   $$\inf_{h\in\mathcal H}R^{\rm in}_D(h)=0,\qquad\inf_{h\in\mathcal H}R^{\rm out}_D(h)=0.$$
--   Then Condition 1 does not hold in $\mathscr D$, and OOD detection is not learnable in $\mathscr D$ for $\mathcal H$.
--
--   **Formalization Note** Definition 4 asks that $D_X\ll\tilde\mu$ and uses the Radon-Nikodym derivatives of both $D_{X_{\rm I}}$ and $D_{X_{\rm O}}$; the formal definition requires $D_{X_{\rm I}}\ll\tilde\mu$ and $D_{X_{\rm O}}\ll\tilde\mu$, which is equivalent when $\pi^{\rm out}>0$ and is what the derivatives need when $\pi^{\rm out}=0$. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 4, Definition 4 and Theorem 3, pp. 5-6; proof in Appendix G.1, pp. 29-31

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem overlap_breaks_linear_condition {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))}
    {K : ℕ} (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h)
    (𝒟 : Set (Domain 𝒳 K)) (h𝒟 : IsPriorUnknown 𝒟) (D : Domain 𝒳 K) (hD : D ∈ 𝒟)
    (hov : HasOverlap D) (hin : (⨅ h ∈ H, riskIn ℓ D h) = 0)
    (hout : (⨅ h ∈ H, riskOut ℓ D h) = 0) :
    ¬ LinearCondition ℓ 𝒟 H ∧ ¬ IsLearnable ℓ 𝒟 H := by sorry

end OODLearnable
