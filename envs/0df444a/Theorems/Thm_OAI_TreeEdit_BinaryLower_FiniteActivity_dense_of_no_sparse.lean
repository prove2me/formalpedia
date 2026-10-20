-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_dense_of_no_sparse
-- name    : OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:36:08.968885+00:00
-- url     : https://prove2.me/theorems/d1f2af14-1a05-4ede-ad9b-fc1734a1154f
-- title:
--   Without sparse nodes the active leaves are numerous
-- statement:
--   Let $\alpha$ be finite, $\mathcal A$ an activity predicate on nodes of the complete $\alpha$-ary tree of depth $h$, and $b\in\mathbb N$. If the root is active and no internal node is sparse (active with fewer than $b$ active children), then
--   $$
--   b^h\le\bigl|\{f:\{1..h\}\to\alpha:\ \mathcal A(f)\ \text{active}\}\bigr| .
--   $$
--
--   Dense branching from an active root forces many active leaves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteActivityBridge.lean#L29-L47

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical

theorem OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse {α : Type*} [Fintype α]
    (active : List α → Prop) (b h : ℕ)
    (hroot : active []) (hno : ¬ ∃ v : InternalNode α h, sparseNode active b v) :
    b ^ h ≤ (Finset.univ.filter fun f : Fin h → α => active (List.ofFn f)).card := by sorry
