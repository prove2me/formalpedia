-- Prove2me | Theorems.Thm_IntMul_OpenAI_partial_swap_bruhat_runs
-- name    : IntMul.OpenAI.partial_swap_bruhat_runs
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:38:29.915983+00:00
-- url     : https://prove2.me/theorems/c6a5db80-7f31-4225-b85f-48df28a8a081
-- title:
--   Bruhat involution of a partial-swap frame
-- statement:
--   Let $K$ be a field and $p$ an $m\times m$ idempotent with a lower–lower Bruhat factorization $p=F_1\pi F_2$: $F_1,F_2$ are lower triangular with nonzero diagonal, and $\pi$ is a $0/1$ matrix with at most one $1$ in each row and each column. Order the $2m$ coordinates as $H_0,\dots,H_{m-1},D_0,\dots,D_{m-1}$, and consider the partial-swap frame
--   $$S_p=\begin{pmatrix}1-p&p\\p&1-p\end{pmatrix}.$$
--   Then $S_p=E_1\,w\,E_2$ with $E_1,E_2$ lower triangular with nonzero diagonal, where $w$ is the permutation matrix
--   $$w=\begin{pmatrix}\operatorname{diag}(\mathbf 1[\text{row }i\text{ of }\pi\text{ empty}])&\pi\\ \pi^{\mathsf T}&\operatorname{diag}(\mathbf 1[\text{column }j\text{ of }\pi\text{ empty}])\end{pmatrix}.$$
--   In words: the Bruhat involution of $S_p$ swaps $H_i\leftrightarrow D_j$ exactly for the pivots $(i,j)$ of $p$, and fixes every other coordinate.
--
--   This is the "runs" principle in Jain's flag-basis note. Frames along the edges of the two-stage bit interchange are partial swaps. By Lemma 10 of the OpenAI preprint, an edge then costs one recursive field interchange per transposition, and a run of consecutive pivots $(i,j),(i+1,j+1),\dots$ is a single interchange of contiguous chunks. So the child widths entering the moment certificates $\sum_w n_w(w/m)^{1-a}$ are read off from the pivots of the idempotents. With `IntMul.OpenAI.idempotent_corner_profile` this gives the partial-swap batching lemma: $m-a$ corner transpositions plus one aligned run of width $2a-m$.
--
--   **Formalization Note** The $2m$ coordinates are `Fin (m + m)` via `finSumFinEquiv` (left summand = $H$). Matrices are blocks built with `Matrix.fromBlocks`.
-- source:
--   S. Jain, integer-mult-kappa, notes/flag-basis.tex (paragraph 'Runs') and notes/partial-swap-batching.tex, https://github.com/Swapnil-jain/integer-mult-kappa ; OpenAI, Integer multiplication below n log n, Lemmas 9-10

import Mathlib
open Matrix

namespace IntMul.OpenAI

theorem partial_swap_bruhat_runs {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (p F₁ π F₂ : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
    (hF₁ : ∀ i j, i < j → F₁ i j = 0) (hd₁ : ∀ i, F₁ i i ≠ 0)
    (hF₂ : ∀ i j, i < j → F₂ i j = 0) (hd₂ : ∀ i, F₂ i i ≠ 0)
    (h01 : ∀ i j, π i j = 0 ∨ π i j = 1)
    (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
    (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i')
    (hfac : p = F₁ * π * F₂) :
    ∃ E₁ E₂ : Matrix (Fin (m + m)) (Fin (m + m)) K,
      (∀ i j, i < j → E₁ i j = 0) ∧ (∀ i, E₁ i i ≠ 0) ∧
      (∀ i j, i < j → E₂ i j = 0) ∧ (∀ i, E₂ i i ≠ 0) ∧
      (Matrix.fromBlocks (1 - p) p p (1 - p)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        E₁ * (Matrix.fromBlocks
            (Matrix.diagonal fun i => if ∃ j, π i j = 1 then (0 : K) else 1) π πᵀ
            (Matrix.diagonal fun j => if ∃ i, π i j = 1 then (0 : K) else 1)).submatrix
              finSumFinEquiv.symm finSumFinEquiv.symm * E₂ := by sorry

end IntMul.OpenAI
