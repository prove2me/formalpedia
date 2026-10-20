-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedRow_sum_length_filter_tag
-- name    : OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:22:55.003996+00:00
-- url     : https://prove2.me/theorems/2c84fd62-15c5-47ea-81da-92328cd8cf03
-- title:
--   Filtering a list by tags partitions its length
-- statement:
--   Let $I$ be a finite set, $\mathrm{tag}:\alpha\to I$, and $z$ a list over $\alpha$. Then
--   $$
--   \sum_{i\in I}\bigl|\{\text{letters of }z\text{ with tag }i\}\bigr|=|z| ,
--   $$
--   where each term is the length of the sublist of letters with tag $i$.
--
--   Every letter is counted once, under its own tag.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean#L56-L70

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

theorem OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag {α I : Type*} [Fintype I] [DecidableEq I]
    (tag : α → I) (z : List α) :
    (∑ i, (z.filter (fun a => decide (tag a = i))).length) = z.length := by sorry
