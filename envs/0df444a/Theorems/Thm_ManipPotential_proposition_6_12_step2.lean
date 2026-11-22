-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_step2
-- name    : ManipPotential.proposition_6_12_step2
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:52:11.692405+00:00
-- url     : https://prove2.me/theorems/4eddf041-c138-47c9-b300-50843a438004
-- title:
--   Proposition 6.12, Step 2 — nearest-point projection constructs a normalized comparison vector
-- statement:
--   Let $m\ge3$, and fix a real $\lambda$, candidates $c_i,c_j$, and a linear subspace $T\subseteq\mathbb R^{\mathcal L(C)}$ of dimension $m!-m+1$. Suppose $M$ is closed and convex, contains $0$, is stable under nonnegative scalar multiplication, contains $T$ and the transfer set $T_{ij}$, and satisfies
--   $$
--   -(\ell_i-\ell_j)\notin M.
--   $$
--   Then there are a linear subspace $W\subseteq\mathbb R^{\mathcal L(C)}$ and a vector $w$ such that
--   $$
--   \dim W=m-1,\qquad w\in W\cap C_{ij},\qquad w\cdot(\ell_i-\ell_j)=1.
--   $$
--   The construction of $W$ depends only on $T$ (it is the orthogonal complement); the candidate-dependent set $M$ is used only to construct $w$. Here $C_{ij}$ is the comparison cone (18)–(19).
--
--   This is exactly Step 2 of Proposition 6.12. Let $p\in M$ minimize the Euclidean distance to $-V$, where $V=\ell_i-\ell_j$, and set $w_0=p+V$. The nearest-point variational inequality gives $w_0\cdot\xi\ge0$ for every $\xi\in M$ and $w_0\cdot V>0$; nonnegativity on $T_{ij}$ is precisely membership in $C_{ij}$, and nonnegativity on both $T$ and $-T$ gives $w_0\in T^\perp$. Division by $w_0\cdot V$ supplies the required normalization.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 2, p.36, especially footnote 19

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

/-- Proposition 6.12, Step 2 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.36): projection onto a closed convex cone containing `T` and the transfer vectors, followed by normalization, produces a comparison vector in the orthogonal complement of `T`. -/
theorem ManipPotential.proposition_6_12_step2 {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (lam : ℝ) (i j : Fin m) (T : Submodule ℝ (Ranking m → ℝ))
    (hTfin : Module.finrank ℝ T = m.factorial - m + 1)
    (M : Set (Ranking m → ℝ))
    (hMc : IsClosed M) (hMx : Convex ℝ M) (hM0 : 0 ∈ M)
    (hMs : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M → a • x ∈ M)
    (hTM : (T : Set (Ranking m → ℝ)) ⊆ M)
    (hUM : TransferVectors lam i j ⊆ M)
    (hV : -(unitVec (ell i) - unitVec (ell j)) ∉ M) :
    ∃ W : Submodule ℝ (Ranking m → ℝ), Module.finrank ℝ W = m - 1 ∧
      ∃ w ∈ W, w ∈ Cmp lam i j ∧
        dotProduct w (unitVec (ell i) - unitVec (ell j)) = 1 := by sorry
