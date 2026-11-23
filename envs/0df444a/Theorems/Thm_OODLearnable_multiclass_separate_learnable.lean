-- Prove2me | Theorems.Thm_OODLearnable_multiclass_separate_learnable
-- name    : OODLearnable.multiclass_separate_learnable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:30:16.539853+00:00
-- url     : https://prove2.me/theorems/aff2020c-5e5a-4b27-8c96-78efe5d8b4bb
-- title:
--   Theorem 7: multi-class OOD detection in the separate space with finite feature space
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be finite, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$ that satisfies Condition 2,
--   $$\ell(y_2,y_1)\le\ell(K+1,y_1)\qquad\text{for all }y_1,y_2\in\mathcal Y,$$
--   let $\mathcal H^{\rm in}$ be a nonempty set of functions $\mathcal X\to\mathcal Y$, and let $\mathcal H^{\rm b}$ be a set of functions $\mathcal X\to\{1,2\}$ with $\mathcal H_{\rm all}\setminus\{h^{\rm out}\}\subseteq\mathcal H^{\rm b}$ ($\mathcal H_{\rm all}$ all functions $\mathcal X\to\{1,2\}$, $h^{\rm out}\equiv2$). Then OOD detection is learnable in the separate space $\mathscr D^s_{XY}$ for $\mathcal H=\mathcal H^{\rm in}\bullet\mathcal H^{\rm b}$.
--
--   **Formalization Note** The nonemptiness of $\mathcal H^{\rm in}$ is implicit in the paper (for $\mathcal H^{\rm in}=\emptyset$ and $\mathcal X\neq\emptyset$ the space $\mathcal H$ is empty and the claim fails). The binary labels $1,2$ are $0,1$ in `Fin 2`. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 5, Theorem 7, eq. (4) and Condition 2, p. 7; proof in Appendix I.2, pp. 38-39

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem multiclass_separate_learnable {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))}
    (h𝒳 : 𝒳.Finite) {K : ℕ} (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (Hin : Set (𝒳 → Fin K)) (hHin : Hin.Nonempty) (Hb : Set (𝒳 → Fin 2))
    (hHmeas : ∀ h ∈ dotSpace Hin Hb, Measurable h)
    (hHb : {g : 𝒳 → Fin 2 | g ≠ fun _ => 1} ⊆ Hb) (hC2 : LossCondition2 ℓ) :
    IsLearnable ℓ (separateSpace : Set (Domain 𝒳 K)) (dotSpace Hin Hb) := by sorry

end OODLearnable
