-- Prove2me | Theorems.Thm_OODLearnable_finite_domain_positive_ood_risk_not_learnable
-- name    : OODLearnable.finite_domain_positive_ood_risk_not_learnable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:28:09.857184+00:00
-- url     : https://prove2.me/theorems/baebeff3-cf30-4b15-a483-325b48e19f40
-- title:
--   Lemma 4: a finite discrete separate domain with positive OOD risk prevents learnability
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, and let $\mathcal H$ be separate for OOD (Assumption 1: every $x\in\mathcal X$ has some $h_x\in\mathcal H$ with $h_x(x)=K+1$). If there is a finite discrete domain $D_{XY}$ in the separate space $\mathscr D^s_{XY}$ with
--   $$\inf_{h\in\mathcal H}R^{\rm out}_D(h)>0,$$
--   then OOD detection is not learnable in $\mathscr D^s_{XY}$ for $\mathcal H$.
--
--   **Formalization Note** "Finite discrete domain" is read as: $D_{X_{\rm I}Y_{\rm I}}$ and $D_{X_{\rm O}}$ are both concentrated on finite sets, which is what the proof uses (it decomposes $D_{X_{\rm O}}$ into finitely many point masses). The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Appendix H, Lemma 4, p. 33; Assumption 1 stated in Section 4, p. 6

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem finite_domain_positive_ood_risk_not_learnable {dim : ℕ}
    {𝒳 : Set (EuclideanSpace ℝ (Fin dim))} {K : ℕ}
    (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h) (hA1 : SeparateForOOD H)
    (D : Domain 𝒳 K) (hD : D ∈ (separateSpace : Set (Domain 𝒳 K))) (hfin : IsFiniteDiscrete D)
    (hout : 0 < ⨅ h ∈ H, riskOut ℓ D h) :
    ¬ IsLearnable ℓ (separateSpace : Set (Domain 𝒳 K)) H := by sorry

end OODLearnable
