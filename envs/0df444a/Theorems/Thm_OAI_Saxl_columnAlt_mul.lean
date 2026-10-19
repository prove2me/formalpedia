-- Prove2me | Theorems.Thm_OAI_Saxl_columnAlt_mul
-- name    : OAI.Saxl.columnAlt_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:54:45.353263+00:00
-- url     : https://prove2.me/theorems/2a682c7c-32f6-4f94-9a8c-dfc5b9bd77c0
-- title:
--   The column antisymmetrizer absorbs column permutations up to their sign
-- statement:
--   Let $\mu$ be a Young diagram, $n,d\in\mathbb{N}$, and $t$ a tableau of shape $\mu$ (a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells of $\mu$). Let $\rho$ be the representation of $S_n$ on the word space $W_{n,d}$ of functions $x$ on words $a:[n]\to[d]$ given by $(\rho(g)x)(a)=x(a\circ g)$, and let $C_t\le S_n$ be the column group of $t$ (the permutations $g$ with $t(g(p))$ in the same column as $t(p)$ for every position $p$). The column antisymmetrizer of $t$ is the operator
--   $$A_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(W_{n,d}).$$
--   The theorem states that for every $h\in C_t$,
--   $$A_t\,\rho(h)=\operatorname{sgn}(h)\,A_t .$$
--
--   This is the basic alternation property of $A_t$. It implies, for example, that $A_t$ annihilates every vector fixed by an odd column permutation, and that $A_t$ takes the same value, up to sign, on all vectors of a $C_t$-orbit. It holds for every alphabet size $d$, not only for $d$ equal to the number of rows of $\mu$.
--
--   **Formalization Note** $A_t$ is `columnAlt t`, an element of `Module.End ℂ (WordSpace n d)`, and the product on the left is composition of endomorphisms; the sign is the complex-valued character `signC`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean#L124-L145

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by sorry
