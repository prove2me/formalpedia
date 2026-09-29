-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_depthAlg_correct
-- name    : HarelTarjan.SymOrder.depthAlg_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:49:11.308391+00:00
-- url     : https://prove2.me/theorems/2d5e9f33-bf92-4d67-bb8e-e0941b2474e1
-- title:
--   The depth algorithm computes the number of the depth-$d_2$ ancestor of $v$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. Let $v$ be a vertex of depth $d_1$, let $d_2 \le d_1$, and let $h = d - d_2$. Let $u$ be the ancestor of $v$ at depth $d_2$ (the prefix of length $d_2$ of the path to $v$). Then $u$ is an ancestor of $v$, has depth $d_2$, and it is the unique vertex with number $2^{h+1} \lfloor \mathrm{sym}(v) / 2^{h+1} \rfloor + 2^h$: for every vertex $x$,
--   $$\mathrm{sym}(x) = 2^{h+1} \left\lfloor \mathrm{sym}(v) / 2^{h+1} \right\rfloor + 2^h \iff x = u,$$
--   so the algorithm to solve the depth problem of §3 (p. 342), which returns $\mathrm{sym}^{-1}$ of this number, returns the ancestor of $v$ whose depth is $d_2$.
--
--   This is Step 2 of the algorithm to compute $\operatorname{nca}(v,w)$; the paper derives it from Lemmas 1 and 3.
--
--   **Formalization Note** $\mathrm{sym}^{-1}(N) = u$ is stated as "a vertex has number $N$ if and only if it is $u$", which asserts both that $N$ is a number of the tree and that $u$ is the vertex carrying it; no inverse function is defined. $d - d_2$ is natural-number subtraction and does not truncate since $d_2 \le d_1 \le d$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, §3, Algorithm to solve the depth problem (unnumbered)

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms

namespace HarelTarjan.SymOrder

/-- The algorithm to solve the depth problem (§3, p. 342) is correct: given a vertex `v` and a
depth `d₂ ≤ depth(v)`, with `h = d − d₂`, the vertex `sym⁻¹(2^{h+1} ⌊sym(v) / 2^{h+1}⌋ + 2^h)`
is the ancestor of `v` whose depth is `d₂`: `ancestorAtDepth v d₂` is an ancestor of `v` of depth
`d₂`, and a vertex `u` has number `2^{h+1} ⌊sym(v) / 2^{h+1}⌋ + 2^h` if and only if it is that
ancestor. -/
theorem depthAlg_correct {d : ℕ} (v : Vertex d) (d₂ : ℕ) (hd₂ : d₂ ≤ depth v) :
    IsAncestor (ancestorAtDepth v d₂) v ∧ depth (ancestorAtDepth v d₂) = d₂ ∧
      ∀ u : Vertex d, sym u = depthAlgNum v d₂ ↔ u = ancestorAtDepth v d₂ := by sorry

end HarelTarjan.SymOrder
