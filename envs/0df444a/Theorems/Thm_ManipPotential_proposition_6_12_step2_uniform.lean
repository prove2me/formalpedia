-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_step2_uniform
-- name    : ManipPotential.proposition_6_12_step2_uniform
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:18.558276+00:00
-- url     : https://prove2.me/theorems/e4c0b41b-b64c-4351-a40d-b18e3e52b224
-- title:
--   Proposition 6.12, Step 2 — one orthogonal complement contains every normalized comparison vector
-- statement:
--   Let $m\ge3$, let $\lambda\in\mathbb R$, and let $T\subseteq\mathbb R^{\mathcal L(C)}$ be a linear subspace of dimension $m!-m+1$. Suppose that for every candidate pair $(i,j)$ a set $M_{ij}$ is given which is closed and convex, contains $0$, is stable under nonnegative scalar multiplication, contains $T$ and $T_{ij}$, and, whenever $i\ne j$, satisfies
--   $$
--   -(\ell_i-\ell_j)\notin M_{ij}.
--   $$
--   Then there is a single linear subspace $W\subseteq\mathbb R^{\mathcal L(C)}$ such that
--   $$
--   \dim W=m-1,
--   $$
--   and for every $i\ne j$ some vector $w_{ij}$ satisfies
--   $$
--   w_{ij}\in W\cap C_{ij},\qquad w_{ij}\cdot(\ell_i-\ell_j)=1.
--   $$
--
--   This combines every application of Step 2 in Proposition 6.12. The common space is $W=T^\perp$, fixed independently of $(i,j)$. For each pair, let $p\in M_{ij}$ minimize the Euclidean distance to $-V$, where $V=\ell_i-\ell_j$, and set $w_0=p+V$. The nearest-point variational inequality gives $w_0\cdot\xi\ge0$ for every $\xi\in M_{ij}$ and $w_0\cdot V>0$. Nonnegativity on $T_{ij}$ is precisely membership in $C_{ij}$, while nonnegativity on both $T$ and $-T$ gives $w_0\in T^\perp$. Finally, $w_{ij}=w_0/(w_0\cdot V)$ has the required normalization.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 2, p.36, especially footnote 19

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

/-- Proposition 6.12, Step 2, uniform formulation (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.36): nearest-point projection onto each closed convex cone `M i j`, followed by normalization, produces comparison vectors all lying in the same orthogonal complement `Tᗮ`. -/
theorem ManipPotential.proposition_6_12_step2_uniform {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (lam : ℝ) (T : Submodule ℝ (Ranking m → ℝ))
    (hTfin : Module.finrank ℝ T = m.factorial - m + 1)
    (M : Fin m → Fin m → Set (Ranking m → ℝ))
    (hMc : ∀ i j, IsClosed (M i j)) (hMx : ∀ i j, Convex ℝ (M i j))
    (hM0 : ∀ i j, 0 ∈ M i j)
    (hMs : ∀ i j ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M i j → a • x ∈ M i j)
    (hTM : ∀ i j, (T : Set (Ranking m → ℝ)) ⊆ M i j)
    (hUM : ∀ i j, TransferVectors lam i j ⊆ M i j)
    (hV : ∀ i j, i ≠ j → -(unitVec (ell i) - unitVec (ell j)) ∉ M i j) :
    ∃ W : Submodule ℝ (Ranking m → ℝ), Module.finrank ℝ W = m - 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ w ∈ W, w ∈ Cmp lam i j ∧
        dotProduct w (unitVec (ell i) - unitVec (ell j)) = 1 := by sorry
