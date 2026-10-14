-- Prove2me | Theorems.Thm_IntMul_OpenAI_partial_perm_eq_of_corner_counts
-- name    : IntMul.OpenAI.partial_perm_eq_of_corner_counts
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:08:45.279247+00:00
-- url     : https://prove2.me/theorems/ff15fb01-f1f6-49d7-88af-3265975791fc
-- title:
--   A 0/1 matrix is determined by its corner counts
-- statement:
--   Let $P,P'$ be $n\times n$ matrices with entries in $\{0,1\}$. Suppose that for all $X,Y\in\mathbb N$ they have the same number of entries equal to $1$ in the northeast corner of rows $<X$ and columns $\ge Y$:
--   $$\#\{(a,b):a<X,\ b\ge Y,\ P_{ab}=1\}=\#\{(a,b):a<X,\ b\ge Y,\ P'_{ab}=1\}.$$
--   Then $P=P'$.
--
--   Each entry is recovered from four corner counts by inclusion–exclusion,
--   $$[P_{ij}=1]=c(i{+}1,j)-c(i,j)-c(i{+}1,j{+}1)+c(i,j{+}1).$$
--   Together with `IntMul.OpenAI.bruhat_rank_profile`, this shows that the partial permutation of a lower–lower Bruhat factorization $A=E_1\Pi E_2$ is unique. So the number and the widths of the recursive interchange calls compiled from an edge matrix are intrinsic to the matrix; this is used by every batching argument for the $\kappa$-saving networks.
--
--   **Formalization Note** The entry type only needs `0`, `1` and decidable equality.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), Section 4.1 (Bruhat factorization); uniqueness of the Bruhat permutation via rank conditions, used in S. Jain, integer-mult-kappa notes/partial-swap-batching.tex

import Mathlib
open Finset

namespace IntMul.OpenAI

theorem partial_perm_eq_of_corner_counts {n : ℕ} {K : Type*} [Zero K] [One K] [DecidableEq K]
    (P P' : Matrix (Fin n) (Fin n) K)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) (h01' : ∀ i j, P' i j = 0 ∨ P' i j = 1)
    (h : ∀ X Y : ℕ,
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card =
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P' x.1 x.2 = 1).card) :
    P = P' := by sorry

end IntMul.OpenAI
