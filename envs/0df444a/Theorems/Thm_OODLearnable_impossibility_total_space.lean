-- Prove2me | Theorems.Thm_OODLearnable_impossibility_total_space
-- name    : OODLearnable.impossibility_total_space
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:27:31.186806+00:00
-- url     : https://prove2.me/theorems/d0e1e40e-467a-4598-850c-bbcaa1bcc09a
-- title:
--   Theorem 4: impossibility theorem for the total space
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, and let $\mathcal H$ be a hypothesis space. Let $\phi$ map the ID labels $1,\dots,K$ to $1$ and the OOD label $K+1$ to $2$. If
--   $$|\phi\circ\mathcal H|>1,$$
--   then OOD detection is not learnable in the total space $\mathscr D^{\rm all}_{XY}$ (all domains) for $\mathcal H$.
--
--   **Formalization Note** $|\phi\circ\mathcal H|$ is the cardinality in $\mathbb N\cup\{\infty\}$ of the set $\{\phi\circ h:h\in\mathcal H\}$. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 4, Theorem 4, p. 6; proof in Appendix G.2, p. 31

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem impossibility_total_space {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))} {K : ℕ}
    (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h)
    (hφ : 1 < (phiComp H).encard) :
    ¬ IsLearnable ℓ (totalSpace : Set (Domain 𝒳 K)) H := by sorry

end OODLearnable
