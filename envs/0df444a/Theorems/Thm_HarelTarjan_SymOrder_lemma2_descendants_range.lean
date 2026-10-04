-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_lemma2_descendants_range
-- name    : HarelTarjan.SymOrder.lemma2_descendants_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:46:55.005769+00:00
-- url     : https://prove2.me/theorems/e53f2e30-cc7c-4b36-81cb-154975573581
-- title:
--   Lemma 2 — the descendants of $v$ have numbers in $[\mathrm{sym}(v)-2^{h(v)}+1, \mathrm{sym}(v)+2^{h(v)}-1]$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. The descendants of a vertex $v$ are exactly the vertices with numbers in the range
--   $$\left[\mathrm{sym}(v) - 2^{h(v)} + 1,\ \mathrm{sym}(v) + 2^{h(v)} - 1\right].$$
--   That is, for all vertices $v, w$: $w$ is a descendant of $v$ if and only if $\mathrm{sym}(v) - 2^{h(v)} + 1 \le \mathrm{sym}(w) \le \mathrm{sym}(v) + 2^{h(v)} - 1$.
--
--   Lemma 2 is the ancestor test of the nca depth algorithm.
--
--   **Formalization Note** The two inequalities are stated additively, $\mathrm{sym}(v) + 1 \le \mathrm{sym}(w) + 2^{h(v)}$ and $\mathrm{sym}(w) + 1 \le \mathrm{sym}(v) + 2^{h(v)}$, which are equivalent over the integers and avoid truncated subtraction.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, Lemma 2

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- Lemma 2 (p. 342): the descendants of vertex `v` are those vertices with numbers in the range
`[sym(v) − 2^{h(v)} + 1, sym(v) + 2^{h(v)} − 1]`. The two endpoint inequalities are written
additively, to avoid truncated subtraction on `ℕ`. -/
theorem lemma2_descendants_range {d : ℕ} (v w : Vertex d) :
    IsAncestor v w ↔
      (sym v + 1 ≤ sym w + 2 ^ height v ∧ sym w + 1 ≤ sym v + 2 ^ height v) := by sorry

end HarelTarjan.SymOrder
