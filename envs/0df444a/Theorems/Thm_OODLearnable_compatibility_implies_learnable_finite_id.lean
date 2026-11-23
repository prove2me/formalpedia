-- Prove2me | Theorems.Thm_OODLearnable_compatibility_implies_learnable_finite_id
-- name    : OODLearnable.compatibility_implies_learnable_finite_id
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:30:54.986927+00:00
-- url     : https://prove2.me/theorems/34fb97ed-38ea-4a81-9d19-23d3117b4779
-- title:
--   Theorem 8 (sufficiency and rate, as proved): compatibility gives learnability in the finite-ID-distribution space
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be bounded, let $\ell$ be a loss with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, let $\mathcal H$ be a nonempty hypothesis space, and let $\mathscr D^F_{XY}$ be a finite-ID-distribution space. If the compatibility condition (Condition 3) holds, then OOD detection is learnable in $\mathscr D^F_{XY}$ for $\mathcal H$; moreover, for every $\theta\in(0,1)$ the learning rate can be taken to be
--   $$\epsilon_{\rm cons}(n)=O\Big(\frac1{\sqrt{n^{1-\theta}}}\Big).$$
--
--   **Formalization Note** Theorem 8 of the paper states an equivalence: learnability in $\mathscr D^F_{XY}$ if and only if Condition 3. Only the direction Condition 3 $\Rightarrow$ learnability, with the rate, is stated here. The proof of the converse picks one sample $S_\epsilon$ for each domain separately and then uses it for the whole equivalence class, and the converse can fail when an equivalence class contains infinitely many OOD distributions (a counterexample is given in the mission report). The rate is formalized as: some valid sequence $\epsilon_{\rm cons}$ satisfies $\epsilon_{\rm cons}(n)\le C/\sqrt{n^{1-\theta}}$ for all $n\ge1$. The hypothesis that $\mathcal H$ is nonempty is implicit in the paper. The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 5, Theorem 8, Definition 5 and Condition 3, p. 7; proof in Appendix J.1 (Lemma 8), pp. 39-41

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem compatibility_implies_learnable_finite_id {dim : ℕ}
    {𝒳 : Set (EuclideanSpace ℝ (Fin dim))} (h𝒳 : Bornology.IsBounded 𝒳) {K : ℕ}
    (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHne : H.Nonempty) (hHmeas : ∀ h ∈ H, Measurable h)
    (𝒟 : Set (Domain 𝒳 K)) (h𝒟 : IsFiniteIDSpace 𝒟) (hC3 : Compatibility ℓ 𝒟 H) :
    IsLearnable ℓ 𝒟 H ∧
      ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
        IsLearnableAtRate ℓ 𝒟 H (fun n => 1 / Real.sqrt ((n : ℝ) ^ (1 - θ))) := by sorry

end OODLearnable
