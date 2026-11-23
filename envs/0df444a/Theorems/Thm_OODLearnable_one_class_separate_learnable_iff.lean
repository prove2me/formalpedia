-- Prove2me | Theorems.Thm_OODLearnable_one_class_separate_learnable_iff
-- name    : OODLearnable.one_class_separate_learnable_iff
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:29:37.585669+00:00
-- url     : https://prove2.me/theorems/ca01bc8a-6b73-444e-b99e-6e1d0feb07aa
-- title:
--   Theorem 6: one-class OOD detection in the separate space with finite feature space
-- statement:
--   Let $K=1$, so that $\mathcal Y_{\rm all}=\{1,2\}$ with $1$ the ID label and $2$ the OOD label. Let $\mathcal X\subseteq\mathbb R^d$ be finite, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, and let $\mathcal H$ be a hypothesis space that is separate for OOD (Assumption 1) and contains the constant function $h^{\rm in}\equiv1$. Then OOD detection is learnable in the separate space $\mathscr D^s_{XY}$ for $\mathcal H$ if and only if
--   $$\mathcal H_{\rm all}\setminus\{h^{\rm out}\}\subseteq\mathcal H,$$
--   where $\mathcal H_{\rm all}$ is the set of all functions $\mathcal X\to\{1,2\}$ and $h^{\rm out}\equiv2$.
--
--   **Formalization Note** The labels $1,2$ are $0,1$ in `Fin 2`. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 5, Theorem 6 and Assumption 1, p. 6; proof in Appendix I.1, pp. 35-38

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem one_class_separate_learnable_iff {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))}
    (h𝒳 : 𝒳.Finite) (ℓ : Fin (1 + 1) → Fin (1 + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (1 + 1))) (hHmeas : ∀ h ∈ H, Measurable h) (hA1 : SeparateForOOD H)
    (hhin : (fun _ => (0 : Fin (1 + 1))) ∈ H) :
    IsLearnable ℓ (separateSpace : Set (Domain 𝒳 1)) H ↔
      {h : 𝒳 → Fin (1 + 1) | h ≠ fun _ => Fin.last 1} ⊆ H := by sorry

end OODLearnable
