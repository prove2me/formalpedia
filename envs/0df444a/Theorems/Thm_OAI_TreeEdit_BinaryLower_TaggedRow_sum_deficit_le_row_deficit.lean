-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedRow_sum_deficit_le_row_deficit
-- name    : OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:23:44.871284+00:00
-- url     : https://prove2.me/theorems/cb8d6d49-3929-49e0-bb25-43fd9254003a
-- title:
--   Block deficits add up to at most the row deficit
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. Let $X_1,\dots,X_m$ and $Y_1,\dots,Y_m$ be words with $|X_i|=B$, where all letters of $X_i$ and of $Y_i$ carry tag $i$. Then
--   $$
--   \sum_{i=1}^m r_B(X_i,Y_i)\le r_{mB}\bigl(X_1\cdots X_m,\ Y_1\cdots Y_m\bigr).
--   $$
--
--   With disjoint block alphabets, a common subsequence of the rows splits into common subsequences of the blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean#L105-L124

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B) :
    (∑ i, deficit B (X i) (Y i)) ≤ deficit (m * B) (row X) (row Y) := by sorry
