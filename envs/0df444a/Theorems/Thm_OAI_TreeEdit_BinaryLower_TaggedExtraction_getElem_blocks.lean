-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedExtraction_getElem_blocks
-- name    : OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:20:42.336469+00:00
-- url     : https://prove2.me/theorems/53cdb666-98bc-490e-80ee-101c2433bbaf
-- title:
--   Indexing into a concatenation of blocks
-- statement:
--   Let $X_1,\dots,X_m$ be words of length $B$ and $\mathrm{blocks}(X)=X_1X_2\cdots X_m$. Then for every block index $i$ and offset $j<B$,
--   $$
--   \mathrm{blocks}(X)_{\,iB+j}=(X_i)_j .
--   $$
--
--   Position $iB+j$ of the concatenation is the $j$-th letter of the $i$-th block.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean#L51-L68

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedExtraction
universe u
variable {α : Type u}

theorem OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks {m B : ℕ} (X : Fin m → Word α B) (i : Fin m) (j : Fin B) :
    (blocks X)[i.val * B + j.val]'(by rw [length_blocks]; exact block_index_lt i j) =
      (X i).val[j.val]'(by rw [(X i).property]; exact j.isLt) := by sorry
