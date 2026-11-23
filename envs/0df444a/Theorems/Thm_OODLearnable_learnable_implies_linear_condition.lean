-- Prove2me | Theorems.Thm_OODLearnable_learnable_implies_linear_condition
-- name    : OODLearnable.learnable_implies_linear_condition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:25:24.103411+00:00
-- url     : https://prove2.me/theorems/ea049e36-19b3-458d-aaad-19accaff256b
-- title:
--   Lemma 1 (Condition 1 part): learnability in a priori-unknown space implies the linear condition
-- statement:
--   Let $\mathscr D$ be a priori-unknown space of domains over $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, and let $\mathcal H$ be a hypothesis space. If OOD detection is learnable in $\mathscr D$ for $\mathcal H$, then the linear condition (Condition 1) holds: for every $D_{XY}\in\mathscr D$ and every $\alpha\in[0,1)$,
--   $$\inf_{h\in\mathcal H}R^\alpha_D(h)=(1-\alpha)\inf_{h\in\mathcal H}R^{\rm in}_D(h)+\alpha\inf_{h\in\mathcal H}R^{\rm out}_D(h).$$
--
--   This is the necessary condition from which the paper's impossibility theorems are derived.
--
--   **Formalization Note** Lemma 1 of the paper asserts that Conditions 1 and 4 hold; only the Condition 1 part is stated here (Condition 4, the multi-linear condition, is not formalized). The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Appendix F, Lemma 1 (Condition 1 part), pp. 26-28; Condition 1 stated in Section 4, p. 5

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem learnable_implies_linear_condition {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))}
    {K : ℕ} (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h) (𝒟 : Set (Domain 𝒳 K))
    (h𝒟 : IsPriorUnknown 𝒟) (hL : IsLearnable ℓ 𝒟 H) :
    LinearCondition ℓ 𝒟 H := by sorry

end OODLearnable
