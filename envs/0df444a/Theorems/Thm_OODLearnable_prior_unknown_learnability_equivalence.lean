-- Prove2me | Theorems.Thm_OODLearnable_prior_unknown_learnability_equivalence
-- name    : OODLearnable.prior_unknown_learnability_equivalence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:24:14.638811+00:00
-- url     : https://prove2.me/theorems/9692d07b-1da0-4ce6-ba62-c22a80586891
-- title:
--   Theorem 1: learnability in priori-unknown spaces
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$, let $\ell$ be a loss on $\mathcal Y_{\rm all}=\{1,\dots,K+1\}$ with $\ell(y_1,y_2)=0$ iff $y_1=y_2$, let $\mathcal H$ be a hypothesis space, and let $\mathscr D$ be any set of domains. Put
--   $$\mathscr D'=\{D^\alpha_{XY}:D_{XY}\in\mathscr D,\ \alpha\in[0,1)\}.$$
--   Then:
--   1. $\mathscr D'$ is a priori-unknown space and $\mathscr D\subseteq\mathscr D'$;
--   2. if $\mathscr D$ is a priori-unknown space, OOD detection is learnable in $\mathscr D$ for $\mathcal H$ (Definition 1) if and only if it is strongly learnable in $\mathscr D$ for $\mathcal H$ (Definition 2);
--   3. OOD detection is strongly learnable in $\mathscr D$ for $\mathcal H$ if and only if it is learnable in $\mathscr D'$ for $\mathcal H$.
--
--   The theorem reduces the study of strong learnability, which controls every mixing weight $\alpha$ at once, to plain learnability in priori-unknown spaces.
--
--   **Formalization Note** The feature space is $\mathcal X\subseteq\mathbb R^d$ with the Borel structure; every hypothesis in $\mathcal H$ is assumed measurable (the paper's implicit convention, needed for the risks to be defined). Domains are triples $(D_{X_{\rm I}Y_{\rm I}},D_{X_{\rm O}},\pi^{\rm out})$; learnability requires the expected risks to be defined (a.e.-measurable integrands).
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 3, Theorem 1, Definitions 1-3, eqs. (2)-(3), p. 4; proof in Appendix E, pp. 24-26

import Mathlib
import Definitions.Def_OODLearnable_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OODLearnable

theorem prior_unknown_learnability_equivalence {dim : ℕ} {𝒳 : Set (EuclideanSpace ℝ (Fin dim))}
    {K : ℕ} (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (hℓ : IsOODLoss ℓ)
    (H : Set (𝒳 → Fin (K + 1))) (hHmeas : ∀ h ∈ H, Measurable h) (𝒟 : Set (Domain 𝒳 K)) :
    (IsPriorUnknown (priorClosure 𝒟) ∧ 𝒟 ⊆ priorClosure 𝒟) ∧
    (IsPriorUnknown 𝒟 → (IsLearnable ℓ 𝒟 H ↔ IsStronglyLearnable ℓ 𝒟 H)) ∧
    (IsStronglyLearnable ℓ 𝒟 H ↔ IsLearnable ℓ (priorClosure 𝒟) H) := by sorry

end OODLearnable
