-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_isOpen_sheetDomain
-- name    : OAI.DoublingHilbert.isOpen_sheetDomain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:18:02.181794+00:00
-- url     : https://prove2.me/theorems/396193c4-8f6a-489a-83d4-ccffec95a0e8
-- title:
--   Sheet domains of the strip construction are open
-- statement:
--   Recall the strip set $S\subseteq\ell^2$: level $j\in\mathbb{N}$ has scale $r_j=1000^{-(j+1)}$, $N_j\ge1$ colors and width factor $W_j\ge1$, and $U_{j,i}\subseteq\mathbb{R}^2$ is the union of the open horizontal strips $\{p:\ qr_j<p_2<(q+1)r_j\}$ and the open vertical strips $\{p:\ qW_jr_j<p_1<(q+1)W_jr_j\}$ over all integers $q$ with $q\bmod N_j=i$. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$, where $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means a displacement of color $i$; the pair $(p,w)$ is admissible if $w_j\le N_j$ and $p\in U_{j,w_j-1}$ for every $j$ with $w_j\neq0$.
--
--   For a tuple $w$, its sheet domain is the set of base points at which $w$ is admissible:
--   $$
--   \Omega_w=\bigl\{p\in\mathbb{R}^2:\ w_j\le N_j\ \text{and}\ p\in U_{j,w_j-1}\ \text{for every } j \text{ with } w_j\neq0\bigr\}.
--   $$
--
--   **Theorem.** For every finitely supported tuple $w$, the set $\Omega_w$ is an open subset of $\mathbb{R}^2$.
--
--   The sheets $p\mapsto f(z(p,w))$ of a hypothetical embedding $f$ of the strip set, where $z(p,w)\in S$ is the point with base coordinates $p$ and displacement tuple $w$, are defined on these domains. Openness is what allows the sheets to be differentiated and lets small squares around points of a domain be chosen inside it.
--
--   **Formalization Note** The statement is `IsOpen (sheetDomain w)` for `w : Tuple`, where the plane `Base` carries the product topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean#L84-L98

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem OAI.DoublingHilbert.isOpen_sheetDomain (w : Tuple) : IsOpen (sheetDomain w) := by sorry
