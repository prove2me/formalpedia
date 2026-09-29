-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_height_numbering
-- name    : HarelTarjan.SymOrder.height_numbering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:45:58.262119+00:00
-- url     : https://prove2.me/theorems/ab7db3e4-e325-4223-aa08-d85abeb34ea5
-- title:
--   The vertices of height $h$ are numbered $2^h, 3\cdot 2^h, 5\cdot 2^h, \dots$ from left to right
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. For any height $h$, the vertices of height $h$ are numbered $2^h, 3\cdot 2^h, 5\cdot 2^h, \dots$ from left to right. Precisely:
--
--   1. every vertex $v$ that is the $j$-th vertex of its depth from the left (counting from $j = 0$) has
--   $$\mathrm{sym}(v) = (2j+1)\cdot 2^{h(v)};$$
--   2. for every height $h \le d$, the set of numbers of the vertices of height $h$ is $\{(2j+1)\cdot 2^h : 0 \le j < 2^{d-h}\}$.
--
--   This is the basic fact about the numbering from which Lemmas 1–4 of §3 are verified.
--
--   **Formalization Note** "The $j$-th vertex from the left" is `leftIndex v = j`, the path to $v$ read as a binary numeral (left $=0$, right $=1$, most significant turn first). The subtraction $d - h$ is on $\mathbb N$ under $h \le d$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 341, §3, last paragraph (unnumbered)

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- The numbers at height `h` (§3, p. 341): the vertices of height `h` are numbered
`2^h, 3·2^h, 5·2^h, …` from left to right. Pointwise, the vertex `v` that is `j`-th from the left
(counting from `0`) among the vertices of its depth has number `(2j + 1)·2^{h(v)}`; and for each
height `h ≤ d` the set of numbers of the vertices of height `h` is
`{(2j + 1)·2^h : 0 ≤ j < 2^{d−h}}`. -/
theorem height_numbering {d : ℕ} :
    (∀ v : Vertex d, sym v = (2 * leftIndex v + 1) * 2 ^ height v) ∧
      ∀ h : ℕ, h ≤ d →
        (Finset.univ.filter (fun v : Vertex d => height v = h)).image sym =
          (Finset.range (2 ^ (d - h))).image (fun j => (2 * j + 1) * 2 ^ h) := by sorry

end HarelTarjan.SymOrder
