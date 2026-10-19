-- Prove2me | Theorems.Thm_OAI_Saxl_polytabloid_rowWord
-- name    : OAI.Saxl.polytabloid_rowWord
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:53:45.174818+00:00
-- url     : https://prove2.me/theorems/239b10c5-1f14-4e02-bef4-c44b48b984ec
-- title:
--   A polytabloid has coefficient one at its own row word
-- statement:
--   Let $\mu$ be a Young diagram with $d$ rows, let $n\in\mathbb{N}$, and let $t$ be a tableau of shape $\mu$, i.e. a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells of $\mu$ (so $n=|\mu|$). Consider the word space $W_{n,d}$ of functions $x$ on words $a:[n]\to[d]$, with basis vectors $e_a$ and the action $(g\cdot x)(a)=x(a\circ g)$ of $S_n$, so that $g\cdot e_a=e_{a\circ g^{-1}}$. The row word $r_t:[n]\to[d]$ sends a position $p$ to the row index of the cell $t(p)$; the column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(p))$ and $t(p)$ lie in the same column for every $p$; and the polytabloid of $t$ is
--   $$e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,d}.$$
--   The theorem states that the coefficient of $e_t$ at the row word itself is one:
--   $$e_t(r_t)=1.$$
--
--   In particular $e_t\neq0$, so the Specht module spanned by the $S_n$-orbit of $e_t$ is nonzero. The normalization is also used whenever a vector of the Specht module is tested against the coordinate $r_t$.
--
--   **Formalization Note** The statement is `polytabloid t (rowWord t) = 1` for `t : Tableau n μ`, where `Tableau n μ` is `Fin n ≃ μ.cells` and $d$ is `μ.colLen 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Basic.lean#L45-L57

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uV uW

theorem OAI.Saxl.polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by sorry
