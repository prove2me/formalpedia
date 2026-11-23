-- Prove2me | Theorems.Thm_OODLearnable_impossibility_separate_space
-- name    : OODLearnable.impossibility_separate_space
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:28:48.419738+00:00
-- url     : https://prove2.me/theorems/70f3ea6a-e181-4dfb-b5d4-459431be4eeb
-- title:
--   Theorem 5: impossibility theorem for the separate space
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, and let $\mathcal H$ be a hypothesis space that is separate for OOD (Assumption 1). Let $\phi$ map the ID labels to $1$ and the OOD label $K+1$ to $2$. If
--   $${\rm VCdim}(\phi\circ\mathcal H)<+\infty\qquad\text{and}\qquad\sup_{h\in\mathcal H}\big|\{x\in\mathcal X:h(x)\in\mathcal Y\}\big|=+\infty,$$
--   then OOD detection is not learnable in the separate space $\mathscr D^s_{XY}$ for $\mathcal H$.
--
--   So, unlike supervised learning, a finite VC dimension does not guarantee learnability of OOD detection even when ID and OOD supports are disjoint.
--
--   **Formalization Note** Cardinalities and the supremum are taken in $\mathbb N\cup\{\infty\}$. Supports in the definition of $\mathscr D^s_{XY}$ are topological supports in $\mathcal X$. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 4, Theorem 5 and Assumption 1, p. 6; proof in Appendix H (Lemmas 3-5), pp. 31-35

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem impossibility_separate_space {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))} {K : ℕ}
    (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h) (hA1 : SeparateForOOD H)
    (hVC : vcDim (phiComp H) < ⊤)
    (hsup : (⨆ h ∈ H, {x | h x ≠ Fin.last K}.encard) = ⊤) :
    ¬ IsLearnable ℓ (separateSpace : Set (Domain 𝒳 K)) H := by sorry

end OODLearnable
