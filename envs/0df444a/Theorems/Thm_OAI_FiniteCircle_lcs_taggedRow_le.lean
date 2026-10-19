-- Prove2me | Theorems.Thm_OAI_FiniteCircle_lcs_taggedRow_le
-- name    : OAI.FiniteCircle.lcs_taggedRow_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:25:46.887371+00:00
-- url     : https://prove2.me/theorems/0ce14d40-48c2-468c-946d-8ce4f8baedcb
-- title:
--   The longest common subsequence of two tagged concatenations is at most the sum over the tags
-- statement:
--   Let $J$ be a finite set and let $j_1,\dots,j_t$ be an enumeration of $J$ that lists every element of $J$ exactly once. For a word $b_1\cdots b_r$ over an alphabet $\beta$ and a tag $j\in J$, write $\tau_j(b_1\cdots b_r)=(j,b_1)\cdots(j,b_r)$ for the word over $J\times\beta$ in which every letter carries the tag $j$. For a family of words $W=(W_j)_{j\in J}$ over $\beta$, the tagged row is the concatenation
--   $$
--   \operatorname{row}(W)=\tau_{j_1}(W_{j_1})\,\tau_{j_2}(W_{j_2})\cdots\tau_{j_t}(W_{j_t}).
--   $$
--   Let $\operatorname{lcs}(u,v)$ denote the length of a longest common subsequence of two words $u,v$.
--
--   **Theorem.** For any two families $W=(W_j)_{j\in J}$ and $U=(U_j)_{j\in J}$ of words over $\beta$,
--   $$
--   \operatorname{lcs}\bigl(\operatorname{row}(W),\operatorname{row}(U)\bigr)\le\sum_{j\in J}\operatorname{lcs}(W_j,U_j).
--   $$
--
--   The tags forbid a common subsequence from pairing a letter of the $j$-th piece of one row with a letter of a different piece of the other row, so a tagged row is at least as far from another tagged row as its pieces are from each other. When $|W_j|=|U_j|$ for all $j$, the theorem is equivalent to the superadditivity of the deficit, $|\operatorname{row}(W)|-\operatorname{lcs}(\operatorname{row}(W),\operatorname{row}(U))\ge\sum_{j}\bigl(|W_j|-\operatorname{lcs}(W_j,U_j)\bigr)$. It is used to propagate separation through the recursive constructions of hard words, whose rows are tagged rows.
--
--   **Formalization Note** The enumeration is a list `js : List J` with the hypotheses `js.Nodup` and that every `j` is a member of `js`; `J` carries `[Fintype J]` and `[DecidableEq J]`. The tagged row is `taggedRow js W = js.flatMap (fun j => (W j).map (fun b => (j, b)))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean#L59-L72

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.lcs_taggedRow_le {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W U : J → List β) :
    lcs (taggedRow js W) (taggedRow js U) ≤ ∑ j : J, lcs (W j) (U j) := by sorry
