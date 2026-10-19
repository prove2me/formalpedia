-- Prove2me | Theorems.Thm_OAI_Saxl_columnAlt_single
-- name    : OAI.Saxl.columnAlt_single
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:56:01.14854+00:00
-- url     : https://prove2.me/theorems/227d643a-579e-4765-860a-babcf0bf803a
-- title:
--   Column antisymmetrization sends every rearranged row word into the line of the polytabloid
-- statement:
--   Let $\mu$ be a Young diagram with $d$ rows, $n\in\mathbb{N}$, and $t$ a tableau of shape $\mu$, i.e. a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells of $\mu$. In the word space $W_{n,d}$ of functions on words $[n]\to[d]$, with $S_n$ acting by $(g\cdot x)(a)=x(a\circ g)$, let $r_t$ be the row word of $t$ ($r_t(p)$ is the row of $t(p)$), $C_t$ the column group of $t$, $A_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g$ the column antisymmetrizer and $e_t=A_t\,e_{r_t}$ the polytabloid. Then for every permutation $g\in S_n$,
--   $$A_t\,e_{r_t\circ g}\in\mathbb{C}\,e_t .$$
--
--   The words $r_t\circ g$ are exactly the rearrangements of the row word, i.e. the row tabloids of shape $\mu$, so the theorem says that $A_t$ maps every row tabloid to a scalar multiple of the polytabloid. This is the key combinatorial input of the classical submodule theorem for Specht modules and of their irreducibility.
--
--   **Formalization Note** The conclusion is membership in `Submodule.span ℂ {polytabloid t}`, and the word $r_t\circ g$ is `rowWord t ∘ g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean#L207-L225

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by sorry
