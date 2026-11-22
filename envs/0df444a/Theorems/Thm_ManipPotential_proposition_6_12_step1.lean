-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_step1
-- name    : ManipPotential.proposition_6_12_step1
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:47:03.507147+00:00
-- url     : https://prove2.me/theorems/958c3ead-22c7-4909-9e88-e8432404e8bf
-- title:
--   Proposition 6.12, Step 1 — the negative cyclic difference is excluded from the closed transfer cone
-- statement:
--   Let $m\ge3$ and let $g$ satisfy the three axioms of Lemma 6.2, with $\lambda=K+1$. There is a linear subspace $T\subseteq\mathbb R^{\mathcal L(C)}$ such that
--   $$
--   \dim T=m!-m+1,
--   $$
--   and for every pair of distinct candidates $c_i,c_j$ there is a set $M=M_{ij}$ satisfying all of the following:
--
--   1. $M$ is closed and convex, contains $0$, and is closed under multiplication by every nonnegative real scalar;
--   2. $T\subseteq M$ and $T_{ij}\subseteq M$, where $T_{ij}$ is the set of transfer vectors (17);
--   3. the negative difference of the two cyclic unit vectors is excluded:
--   $$
--   -(\ell_i-\ell_j)\notin M.
--   $$
--
--   The space $T$ is fixed before the candidate pair is chosen. In the paper $M$ is $\operatorname{cl}(\operatorname{span}_{\ge0}(T_{ij})+T)$; the formulation here retains exactly the properties used in Step 2 of Proposition 6.12. The excluded vector is the conclusion (21), established by the reference-curve argument and Lemma 6.10.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, Eq. (21), pp.35–36

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

/-- Proposition 6.12, Step 1 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), pp.35–36, Eq. (21)): for each pair `(i,j)`, the vector `-(ℓ_i - ℓ_j)` lies outside a closed convex cone containing both the transfer vectors and the common tangent space `T`. The same `T`, of dimension `m! - m + 1`, works for every pair. -/
theorem ManipPotential.proposition_6_12_step1 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ T : Submodule ℝ (Ranking m → ℝ),
      Module.finrank ℝ T = m.factorial - m + 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ M : Set (Ranking m → ℝ),
        IsClosed M ∧ Convex ℝ M ∧ 0 ∈ M ∧
        (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M → a • x ∈ M) ∧
        (T : Set (Ranking m → ℝ)) ⊆ M ∧
        TransferVectors ((K : ℝ) + 1) i j ⊆ M ∧
        -(unitVec (ell i) - unitVec (ell j)) ∉ M := by sorry
