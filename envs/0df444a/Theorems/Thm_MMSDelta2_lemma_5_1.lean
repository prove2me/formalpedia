-- Prove2me | Theorems.Thm_MMSDelta2_lemma_5_1
-- name    : MMSDelta2.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:47.610453+00:00
-- url     : https://prove2.me/theorems/26339a6a-5904-4d34-b2db-a1171c0ad71a
-- title:
--   Lemma 5.1 — properties [P1]–[P8] of the KPW matrix $M=S+T$
-- statement:
--   The matrix $M=S+T$ satisfies the following properties.
--
--   1. **[P1]** For all $i,j\in[5]$, $M_{i,j}\ge0$; moreover $M_{i,j}>0$ whenever $S_{i,j}\ne0$ or $T_{i,j}\ne0$.
--   2. **[P2]** For all $i,j\in[5]$, $|M_{i,j}-S_{i,j}|<\tfrac1{640}$.
--   3. **[P3]** Every row and every column of $M$ sums to $1$.
--   4. **[P4]** Let $i\in[4]$. If $X\subseteq M^+$ satisfies $(i,i)\in X$ and $M(X)=1$, then exactly one of the following holds: (a) $(i,5)\in X$; (b) $(5,i)\in X$; (c) $(1,5),\dots,(i-1,5),(5,5)\in X$; (d) $(5,1),\dots,(5,i-1),(5,5)\in X$; (e) there are $j,k<i$ with $(j,5),(5,k)\in X$.
--   5. **[P5]** For $i\in[3]$, if $X\subseteq M^+$ and $M(X)=r_i$, then $X=\{(1,2)\}$ for $i=1$ and $X=\{(i,i-1),(i,i+1)\}$ for $i=2,3$.
--   6. **[P6]** For $i\in[3]$, if $X\subseteq M^+$ and $M(X)=c_i$, then $X=\{(2,1)\}$ for $i=1$ and $X=\{(i-1,i),(i+1,i)\}$ for $i=2,3$.
--   7. **[P7]** If $X\subseteq M^+$ and $M(X)=x$, then $X=\{(3,4)\}$.
--   8. **[P8]** If $X\subseteq M^+$ and $M(X)=y$, then $X=\{(4,3)\}$.
--
--   These structural properties drive the rigidity of the core (Lemma 5.2).
--
--   **Formalization Note** Indices are 0-based in Lean (the paper's index $k$ is $k-1$); for $i=1$ the lists in (c) and (d) are empty, so both read $(5,5)\in X$.
--
--   Differences from the source:
--   - encoding: 1-based indices i, j ∈ [5], r_i, c_i for i ∈ [3] → 0-based Fin 5 and Fin 3; [P5], [P6] list the cases i = 1, 2, 3 explicitly; 'exactly one' as ∃! over the five alternatives; reason: same statements
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 5.1, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_MMSDelta2_KPW

namespace MMSDelta2

/-- **Lemma 5.1**, pp.14–15 (PDF pp.16–17).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

The matrix `M = S + T` satisfies:
* [P1] `M_{i,j} ≥ 0` for all `i, j`, and `M_{i,j} > 0` whenever `S_{i,j} ≠ 0` or `T_{i,j} ≠ 0`;
* [P2] `|M_{i,j} − S_{i,j}| < 1/640` for all `i, j`;
* [P3] every row and every column of `M` sums to `1`;
* [P4] for `i ∈ [4]`, if `X ⊆ M⁺`, `(i,i) ∈ X` and `M(X) = 1`, then exactly one of (a) `(i,5) ∈ X`;
  (b) `(5,i) ∈ X`; (c) `(1,5), …, (i−1,5), (5,5) ∈ X`; (d) `(5,1), …, (5,i−1), (5,5) ∈ X`;
  (e) `(j,5), (5,k) ∈ X` for some `j, k < i` holds;
* [P5] for `i ∈ [3]`, `M(X) = r_i` with `X ⊆ M⁺` forces `X = {(1,2)}` (`i = 1`) or
  `X = {(i,i−1), (i,i+1)}` (`i = 2, 3`);
* [P6] for `i ∈ [3]`, `M(X) = c_i` forces `X = {(2,1)}` (`i = 1`) or `X = {(i−1,i), (i+1,i)}`;
* [P7] `M(X) = x` forces `X = {(3,4)}`; [P8] `M(X) = y` forces `X = {(4,3)}`.

**Formalization Note.** Indices are 0-based: the paper's row/column `k` is `k − 1` here, so
`i ∈ [4]` is `i ≠ 4`, position `5` is `4`, and the paper's `r_i`, `c_i` are `kpwR (i−1)`,
`kpwC (i−1)`. "Exactly one of (a)–(e)" is `∃!` over the five alternatives. For `i = 1` the lists
in (c) and (d) are empty. [P5] and [P6] list the three cases `i = 1, 2, 3` explicitly. -/
theorem lemma_5_1 :
    (∀ i j, 0 ≤ kpwM i j ∧ ((kpwS i j ≠ 0 ∨ kpwT i j ≠ 0) → 0 < kpwM i j)) ∧
    (∀ i j, |kpwM i j - kpwS i j| < 1 / 640) ∧
    (∀ i, ∑ j, kpwM i j = 1) ∧ (∀ j, ∑ i, kpwM i j = 1) ∧
    (∀ i : Fin 5, i ≠ 4 → ∀ X ⊆ kpwMplus, (i, i) ∈ X → kpwMsum X = 1 →
      ∃! t : Fin 5, (![(i, 4) ∈ X,
        (4, i) ∈ X,
        (∀ h : Fin 5, h < i → (h, 4) ∈ X) ∧ (4, 4) ∈ X,
        (∀ h : Fin 5, h < i → (4, h) ∈ X) ∧ (4, 4) ∈ X,
        ∃ j k : Fin 5, j < i ∧ k < i ∧ (j, 4) ∈ X ∧ (4, k) ∈ X] : Fin 5 → Prop) t) ∧
    (∀ k : Fin 3, ∀ X ⊆ kpwMplus, kpwMsum X = kpwR k →
      X = (![{(0, 1)}, {(1, 0), (1, 2)}, {(2, 1), (2, 3)}] : Fin 3 → Finset (Fin 5 × Fin 5)) k) ∧
    (∀ k : Fin 3, ∀ X ⊆ kpwMplus, kpwMsum X = kpwC k →
      X = (![{(1, 0)}, {(0, 1), (2, 1)}, {(1, 2), (3, 2)}] : Fin 3 → Finset (Fin 5 × Fin 5)) k) ∧
    (∀ X ⊆ kpwMplus, kpwMsum X = kpwX → X = {(2, 3)}) ∧
    (∀ X ⊆ kpwMplus, kpwMsum X = kpwY → X = {(3, 2)}) := by sorry

end MMSDelta2
