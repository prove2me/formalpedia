-- Prove2me | Theorems.Thm_OAI_FiniteCircle_get_flatMap_uniform
-- name    : OAI.FiniteCircle.get_flatMap_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:27:45.450365+00:00
-- url     : https://prove2.me/theorems/9afa2b91-da70-4594-972d-6c1a683c7d66
-- title:
--   Locating a letter of a concatenation of equal-length words by division with remainder
-- statement:
--   Let $a_0,a_1,\dots,a_{n-1}$ be a list of elements of a set $\alpha$, let $f$ map each element of $\alpha$ to a word over an alphabet $\beta$, and let $L\in\mathbb{N}$ be such that $|f(a_k)|=L$ for every entry $a_k$ of the list. Let
--   $$
--   w=f(a_0)\,f(a_1)\cdots f(a_{n-1})
--   $$
--   be the concatenation of the images, a word of length $nL$, and write $w_k$ for its letter at position $k$ (positions start at $0$). Assume moreover $L\ge1$.
--
--   **Theorem.** For every position $0\le k<|w|$ there are an index $i<n$ and a position $b<|f(a_i)|$ such that
--   $$
--   i=\Bigl\lfloor\frac{k}{L}\Bigr\rfloor,\qquad b=k\bmod L,\qquad w_k=f(a_i)_b .
--   $$
--
--   In words: the letter at position $k$ of the concatenation is the letter at position $k\bmod L$ of the block with index $\lfloor k/L\rfloor$. This is how properties of single letters of recursively built words, for instance the position tags they carry, are read off from the blocks they come from.
--
--   **Formalization Note** The position is `k : Fin (xs.flatMap f).length`, the index `i : Fin xs.length` and the inner position `b : Fin (f (xs.get i)).length`; letters are accessed with `List.get`. The hypothesis `0 < L` is needed for the division to locate a valid block.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean#L321-L349

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.get_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) {L : ℕ}
    (hL : 0 < L) (hl : ∀ a ∈ xs, (f a).length = L)
    (k : Fin (xs.flatMap f).length) :
    ∃ (i : Fin xs.length) (b : Fin (f (xs.get i)).length),
      i.val = k.val/L ∧ b.val = k.val%L ∧ (xs.flatMap f).get k = (f (xs.get i)).get b := by sorry
