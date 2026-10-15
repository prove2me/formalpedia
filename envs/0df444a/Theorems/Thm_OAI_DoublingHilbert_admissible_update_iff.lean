-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_admissible_update_iff
-- name    : OAI.DoublingHilbert.admissible_update_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:18:56.378655+00:00
-- url     : https://prove2.me/theorems/9a2d3b25-73cf-4dfb-bd3a-2091b08d1c3c
-- title:
--   Adding a color-$i$ displacement at an unused level cuts the sheet domain down to $U_{j,i}$
-- statement:
--   Recall the strip set $S\subseteq\ell^2$: level $j\in\mathbb{N}$ has scale $r_j=1000^{-(j+1)}$, $N_j\ge1$ colors and width factor $W_j\ge1$, and $U_{j,i}\subseteq\mathbb{R}^2$ is the union of the open horizontal strips $\{p:\ qr_j<p_2<(q+1)r_j\}$ and the open vertical strips $\{p:\ qW_jr_j<p_1<(q+1)W_jr_j\}$ over all integers $q$ with $q\bmod N_j=i$. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$, where $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means a displacement of color $i$; the pair $(p,w)$ is admissible if $w_j\le N_j$ and $p\in U_{j,w_j-1}$ for every $j$ with $w_j\neq0$.
--
--   For a tuple $w$, a level $j$ and $i\in\mathbb{N}$, let $w[j\mapsto i+1]$ be the tuple that agrees with $w$ except at level $j$, where its entry is $i+1$; it describes the displacement of color $i$ at level $j$ added to $w$.
--
--   **Theorem.** Let $p\in\mathbb{R}^2$, let $w$ be a tuple, let $j,i\in\mathbb{N}$, and assume $w_j=0$. Then
--   $$
--   \bigl(p,\ w[j\mapsto i+1]\bigr)\ \text{is admissible}\iff (p,w)\ \text{is admissible},\quad i<N_j,\quad\text{and}\quad p\in U_{j,i}.
--   $$
--
--   In other words, adding a color-$i$ displacement at an unused level $j$ (with $i<N_j$) replaces the sheet domain $\Omega_w$ by $\Omega_w\cap U_{j,i}$. This identifies the domain of the added sheets compared with a given sheet in the non-embedding argument: one and the same added sheet is defined on the horizontal and on the vertical strips of color $i$.
--
--   **Formalization Note** The modified tuple is `w.update j (i + 1)` (`Finsupp.update`), and $p\in U_{j,i}$ is the predicate `allowed j i p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean#L177-L198

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem OAI.DoublingHilbert.admissible_update_iff (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    admissible p (w.update j (i + 1)) ↔
      admissible p w ∧ i < colors j ∧ allowed j i p := by sorry
