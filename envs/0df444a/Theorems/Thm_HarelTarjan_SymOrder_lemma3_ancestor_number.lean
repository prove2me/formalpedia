-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_lemma3_ancestor_number
-- name    : HarelTarjan.SymOrder.lemma3_ancestor_number
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:47:31.108234+00:00
-- url     : https://prove2.me/theorems/2002f0f4-b2b1-4e95-a4fe-e4e2a286b9c5
-- title:
--   Lemma 3 — the height-$h$ ancestor of $v$ has number $2^{h+1}\lfloor \mathrm{sym}(v)/2^{h+1}\rfloor + 2^h$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. If $v$ is a vertex and $h$ is a height ($h \le d$) such that $h \ge h(v)$, then $v$ has an ancestor of height $h$, and the ancestor $u$ of $v$ of height $h$ has number
--   $$\mathrm{sym}(u) = 2^{h+1} \left\lfloor \mathrm{sym}(v) / 2^{h+1} \right\rfloor + 2^h.$$
--
--   Lemma 3 is the arithmetic behind the depth algorithm: an ancestor is found from the number of $v$ by clearing low-order bits.
--
--   **Formalization Note** "$h$ is a height" is made explicit as $h \le d$. The existence of the ancestor, presupposed by "the ancestor", is stated as a conjunct. The floor is natural-number division.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, Lemma 3

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- Lemma 3 (p. 342): if `v` is a vertex and `h` is a height (`h ≤ d`) such that `h ≥ h(v)`, then
`v` has an ancestor of height `h`, and the ancestor of `v` of height `h` has number
`2^{h+1} ⌊sym(v) / 2^{h+1}⌋ + 2^h` (`/` is floor division on `ℕ`). -/
theorem lemma3_ancestor_number {d : ℕ} (v : Vertex d) (h : ℕ) (hvh : height v ≤ h)
    (hhd : h ≤ d) :
    (∃ u : Vertex d, IsAncestor u v ∧ height u = h) ∧
      ∀ u : Vertex d, IsAncestor u v → height u = h →
        sym u = 2 ^ (h + 1) * (sym v / 2 ^ (h + 1)) + 2 ^ h := by sorry

end HarelTarjan.SymOrder
