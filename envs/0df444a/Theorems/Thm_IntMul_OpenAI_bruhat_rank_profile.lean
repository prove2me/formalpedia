-- Prove2me | Theorems.Thm_IntMul_OpenAI_bruhat_rank_profile
-- name    : IntMul.OpenAI.bruhat_rank_profile
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:02:26.503991+00:00
-- url     : https://prove2.me/theorems/e1e65159-c5e9-4e13-a1b1-e627a8d58760
-- title:
--   Corner ranks determine the lower–lower Bruhat permutation
-- statement:
--   Let $K$ be a field and let $A=E_1\,\Pi\,E_2$ be an $m\times m$ matrix, where $E_1,E_2$ are lower triangular with nonzero diagonal and $\Pi$ is a partial permutation matrix ($0/1$ entries, at most one $1$ in each row and column). Then for all indices $i,j$,
--   $$\operatorname{rank}A[\,0..i,\ j..m-1\,] \;=\; \#\{(a,b)\;:\;a\le i,\ b\ge j,\ \Pi_{ab}=1\},$$
--   where $A[\,0..i,\ j..m-1\,]$ is the submatrix of rows $\le i$ and columns $\ge j$.
--
--   So the partial permutation of a lower–lower Bruhat factorization (which exists by `IntMul.OpenAI.lower_triangular_factorization`) is determined by $A$ alone, through these northeast-corner ranks. The batched-recursion arguments for the $\kappa$-saving networks, such as the partial-swap batching lemma, the flag basis and the reversed-run (opposite bank order) compile of Jain's rounds, read off the recursive interchange calls of an edge from this *Bruhat profile*: a pivot $(a,b)$ is one interchange of the fields $H_a,D_b$, and an order-preserving run of pivots is one batched call.
--
--   **Formalization Note** Rows $\le i$ and columns $\ge j$ are indexed by the subtypes `{r // r ≤ i}` and `{c // j ≤ c}` of `Fin m`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), Lemmas 9-10 (Section 4.1); S. Jain, integer-mult-kappa notes/partial-swap-batching.tex (Bruhat permutation determined by block ranks), https://github.com/Swapnil-jain/integer-mult-kappa

import Mathlib
open Matrix Finset

namespace IntMul.OpenAI

theorem bruhat_rank_profile {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (E₁ P E₂ : Matrix (Fin m) (Fin m) K)
    (hE₁ : ∀ i j, i < j → E₁ i j = 0) (hd₁ : ∀ i, E₁ i i ≠ 0)
    (hE₂ : ∀ i j, i < j → E₂ i j = 0) (hd₂ : ∀ i, E₂ i i ≠ 0)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') (i j : Fin m) :
    ((E₁ * P * E₂).submatrix (fun r : {r : Fin m // r ≤ i} => r.1)
        (fun c : {c : Fin m // j ≤ c} => c.1)).rank =
      (univ.filter fun x : Fin m × Fin m => x.1 ≤ i ∧ j ≤ x.2 ∧ P x.1 x.2 = 1).card := by sorry

end IntMul.OpenAI
