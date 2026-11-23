-- Prove2me | Theorems.Thm_OODLearnable_single_distribution_learnable_iff_linear
-- name    : OODLearnable.single_distribution_learnable_iff_linear
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:26:13.898132+00:00
-- url     : https://prove2.me/theorems/3b637552-28c9-4a66-8d82-b45eefbe9efa
-- title:
--   Theorem 2: learnability in the single-distribution space iff the linear condition
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, let $\mathcal H$ be a nonempty hypothesis space and let $D_{XY}$ be a domain. OOD detection is learnable in the single-distribution space
--   $$\mathscr D^{D_{XY}}_{XY}=\{D^\alpha_{XY}:\alpha\in[0,1)\}$$
--   for $\mathcal H$ if and only if the linear condition (Condition 1) holds in $\mathscr D^{D_{XY}}_{XY}$, that is,
--   $$\inf_{h\in\mathcal H}R^\alpha_D(h)=(1-\alpha)\inf_{h\in\mathcal H}R^{\rm in}_D(h)+\alpha\inf_{h\in\mathcal H}R^{\rm out}_D(h)\qquad\text{for all }\alpha\in[0,1).$$
--
--   **Formalization Note** The hypothesis that $\mathcal H$ is nonempty is implicit in the paper: for $\mathcal H=\emptyset$ both infima are $+\infty$, Condition 1 holds, and no algorithm with values in $\mathcal H$ exists. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 4, Theorem 2 and Condition 1, p. 5; proof in Appendix F (Lemmas 1-2), pp. 26-29

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem single_distribution_learnable_iff_linear {dim : ℕ}
    {𝒳 : Set (EuclideanSpace ℝ (Fin dim))} {K : ℕ}
    (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHne : H.Nonempty) (hHmeas : ∀ h ∈ H, Measurable h)
    (D : Domain 𝒳 K) :
    IsLearnable ℓ (singleSpace D) H ↔ LinearCondition ℓ (singleSpace D) H := by sorry

end OODLearnable
