-- Prove2me | Theorems.Thm_OAI_FiniteCircle_segment_flatMap_uniform
-- name    : OAI.FiniteCircle.segment_flatMap_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:25:27.218579+00:00
-- url     : https://prove2.me/theorems/857e9007-410c-4817-9f13-f8011177fb55
-- title:
--   The $i$-th block of a concatenation of words of equal length
-- statement:
--   Let $a_0,a_1,\dots,a_{n-1}$ be a list of elements of a set $\alpha$, let $f$ map each element of $\alpha$ to a word over an alphabet $\beta$, and let $L\in\mathbb{N}$ be such that $|f(a_k)|=L$ for every entry $a_k$ of the list. Let
--   $$
--   w=f(a_0)\,f(a_1)\cdots f(a_{n-1})
--   $$
--   be the concatenation of the images, a word of length $nL$, and write $w_k$ for its letter at position $k$ (positions start at $0$). For $p,\ell\in\mathbb{N}$, $w[p,p+\ell)$ denotes the segment of $w$ of length $\ell$ starting at position $p$ (the word $w_p\cdots w_{p+\ell-1}$, truncated at the end of $w$).
--
--   **Theorem.** For every index $0\le i<n$,
--   $$
--   w[iL,\ iL+L)=f(a_i).
--   $$
--
--   This is the basic bookkeeping identity for words built by concatenating blocks of a common length, such as the rows of the recursively defined hard words: the $i$-th block of length $L$ of the concatenation is exactly the image of the $i$-th entry. It is the form in which hypotheses about rows, stated for segments $x[iW,iW+W)$, are connected with the recursive definition of the words.
--
--   **Formalization Note** The concatenation is `xs.flatMap f` and the segment is `segment (xs.flatMap f) (i*L) L`, where `segment x p l` is `(x.drop p).take l`; the index is `i : Fin xs.length`, and the entry is `xs.get i`. The value $L=0$ is allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean#L305-L319

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.segment_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) (L : ℕ)
    (hl : ∀ a ∈ xs, (f a).length = L) (i : Fin xs.length) :
    segment (xs.flatMap f) (i.val*L) L = f (xs.get i) := by sorry
