-- Prove2me | Theorems.Thm_IntMul_OpenAI_partial_swap_corner_ranks
-- name    : IntMul.OpenAI.partial_swap_corner_ranks
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:21:31.550321+00:00
-- url     : https://prove2.me/theorems/6993ad47-db80-4179-a152-ca0a34b75b7a
-- title:
--   Corner ranks of a partial-swap frame
-- statement:
--   Let $K$ be a field and $p$ an $m\times m$ idempotent matrix ($p^2=p$), and put $q=1-p$. The *partial swap* frame on paired fields $(H,D)$ is the $2m\times 2m$ matrix
--   $$S_p=\begin{pmatrix}q&p\\p&q\end{pmatrix},$$
--   with rows and columns ordered $H_0,\dots,H_{m-1},D_0,\dots,D_{m-1}$. For $X,Y\in\mathbb N$ write $p[{<}X,{\ge}Y]$ for the block of rows $<X$ and columns $\ge Y$. The northeast corners of $S_p$ have the following ranks:
--
--   - **(B)** rows $H_{<X}$, columns $H_{\ge Y}\cup D$: $\ \#[Y,X)+\operatorname{rank}p[{<}\min(X,Y),\,\cdot\,]$;
--   - **(C)** rows $H\cup D_{<X}$, columns $D_{\ge Y}$: $\ \#[Y,X)+\operatorname{rank}p[\,\cdot\,,{\ge}\max(X,Y)]$;
--   - **(D)** rows $H\cup D_{<X}$, columns $H_{\ge Y}\cup D$: $\ \#\{c\ge Y\}+\min(X,m)+\operatorname{rank}p[{<}Y,{\ge}X]$.
--
--   The remaining corners (rows in $H$, columns in $D$) are blocks of $p$ itself. Combined with `IntMul.OpenAI.bruhat_rank_profile` and `IntMul.OpenAI.partial_perm_eq_of_corner_counts`, these formulas show that the lower–lower Bruhat involution of $S_p$ can be read off from the Bruhat pivots of $p$: it swaps $H_i\leftrightarrow D_j$ for every pivot $(i,j)$ of $p$ and fixes all other coordinates. This is the "runs" principle of Jain's flag-basis and partial-swap batching notes: a frame change $S_p$ on an edge of the two-stage bit interchange costs exactly $\operatorname{rank}p$ field transpositions, grouped into runs that follow the pivots of $p$.
--
--   **Formalization Note** The blocks are written with `Matrix.of` on sum and subtype index types; $\#[Y,X)$ counts $c\in$ `Fin m` with $Y\le c<X$.
-- source:
--   S. Jain, integer-mult-kappa, notes/flag-basis.tex ('Runs') and notes/partial-swap-batching.tex, https://github.com/Swapnil-jain/integer-mult-kappa ; frames S_p from the two-stage bit motif (Paureel's fork of CrocSwap/integer-mult-bounds); OpenAI, Integer multiplication below n log n, Section 4

import Mathlib

namespace IntMul.OpenAI

theorem partial_swap_corner_ranks {m : ℕ} {K : Type*} [Field K] (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
    (X Y : ℕ) :
    -- (B) rows H_{<X}, columns H_{≥Y} ⊕ D
    (Matrix.of fun (r : {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun c => (1 - p) r.1 c.1) (fun c => p r.1 c) c).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix (fun r : {r : Fin m // r.val < min X Y} => r.1) id).rank ∧
    -- (C) rows H ⊕ D_{<X}, columns D_{≥Y}
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val}) =>
        Sum.elim (fun r => p r c.1) (fun r => (1 - p) r.1 c.1) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix id (fun c : {c : Fin m // max X Y ≤ c.val} => c.1)).rank ∧
    -- (D) rows H ⊕ D_{<X}, columns H_{≥Y} ⊕ D
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun r => Sum.elim (fun c => (1 - p) r c.1) (fun c => p r c) c)
          (fun r => Sum.elim (fun c => p r.1 c.1) (fun c => (1 - p) r.1 c) c) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val).card + min X m +
      (p.submatrix (fun r : {r : Fin m // r.val < Y} => r.1) (fun c : {c : Fin m // X ≤ c.val} => c.1)).rank := by sorry

end IntMul.OpenAI
