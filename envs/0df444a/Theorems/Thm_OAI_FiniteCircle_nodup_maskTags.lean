-- Prove2me | Theorems.Thm_OAI_FiniteCircle_nodup_maskTags
-- name    : OAI.FiniteCircle.nodup_maskTags
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:29:42.066011+00:00
-- url     : https://prove2.me/theorems/ace2d8dc-ffd0-45a8-8ddb-3e938ffb0367
-- title:
--   The lexicographic list of mask tags has no repetitions
-- statement:
--   Let $h,l\in\mathbb{N}$ and let $p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ be an arbitrary function. A mask tag at level $l$ is a pair $(k,b)$ with $0\le k<h$ and $0\le b<p(l,k)$; the range of the second coordinate depends on the first. The mask-tag list at level $l$ is the lexicographic enumeration of all mask tags,
--   $$
--   T_l=\bigl((0,0),(0,1),\dots,(0,p(l,0)-1),\ (1,0),\dots,(1,p(l,1)-1),\ \dots,\ (h-1,0),\dots,(h-1,p(l,h-1)-1)\bigr),
--   $$
--   that is, the concatenation over $k=0,1,\dots,h-1$ of the lists $\bigl((k,0),(k,1),\dots,(k,p(l,k)-1)\bigr)$.
--
--   **Theorem.** The list $T_l$ has no repeated entries.
--
--   Together with the fact that every mask tag occurs in $T_l$, this says that $T_l$ enumerates the mask tags exactly once each. In the mask construction of hard words, the rows of the words of level $l\ge1$ are tagged rows indexed by $T_l$, and an enumeration without repetitions is precisely what is needed to split longest common subsequences of such rows tag by tag.
--
--   **Formalization Note** Mask tags form the dependent pair type `MaskTag h p l`, with first component in `Fin h` and second in `Fin (p l k)`, and `maskTags h p l` is the flattening of `List.ofFn` lists; the theorem is the statement `(maskTags h p l).Nodup`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L19-L41

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.nodup_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    (maskTags h p l).Nodup := by sorry
