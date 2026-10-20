-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_lower_bound
-- name    : OAI.TreeEdit.BinaryLower.common_sublist_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:18:31.212407+00:00
-- url     : https://prove2.me/theorems/b9a09fa9-5499-47f9-ad63-5bc1056e9e51
-- title:
--   Two sublists of one word share a long common sublist
-- statement:
--   If $u$ and $v$ are both sublists of a list $w$, then there is a common sublist $z$ of $u$ and $v$ with
--   $$
--   |u|+|v|\le|w|+|z| .
--   $$
--
--   This is inclusion–exclusion for the sets of positions used by $u$ and $v$ in $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/LCSCore.lean#L12-L44

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower

theorem OAI.TreeEdit.BinaryLower.common_sublist_lower_bound {α : Type*} {u v w : List α}
    (hu : u.Sublist w) (hv : v.Sublist w) :
    ∃ z : List α, z.Sublist u ∧ z.Sublist v ∧
      u.length + v.length ≤ w.length + z.length := by sorry
