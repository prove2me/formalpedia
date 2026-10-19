-- Prove2me | Theorems.Thm_OAI_Saxl_columnAlt_collision
-- name    : OAI.Saxl.columnAlt_collision
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:55:22.806459+00:00
-- url     : https://prove2.me/theorems/3660e258-1d27-433a-b82f-8dcaca439d82
-- title:
--   The column antisymmetrizer kills a word with a repeated letter in one column
-- statement:
--   Let $\mu$ be a Young diagram, $n,d\in\mathbb{N}$, and $t$ a tableau of shape $\mu$ (a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells of $\mu$). On the word space $W_{n,d}$ of functions on words $[n]\to[d]$, where $S_n$ acts by $(g\cdot x)(a)=x(a\circ g)$, let $A_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g$ be the column antisymmetrizer, $C_t$ being the group of permutations that preserve the column of $t(p)$ for every position $p$. Let $a:[n]\to[d]$ be a word with basis vector $e_a$. If there are two distinct positions $i\neq j$ such that $t(i)$ and $t(j)$ lie in the same column of $\mu$ and $a$ has the same letter at both, $a(i)=a(j)$, then
--   $$A_t\,e_a=0.$$
--
--   This is the vanishing half of the standard analysis of $A_t$ on words: unless a word has distinct letters at the positions of each column of $t$, its column antisymmetrization is zero.
--
--   **Formalization Note** The statement is `columnAlt t (Pi.single a 1) = 0`; the positions are `i j : Fin n` with `i ≠ j`, and "same column" is equality of the second coordinates of the cells `t i` and `t j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean#L175-L192

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.columnAlt_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by sorry
