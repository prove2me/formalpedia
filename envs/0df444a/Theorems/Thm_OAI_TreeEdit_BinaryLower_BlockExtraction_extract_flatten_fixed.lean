-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_BlockExtraction_extract_flatten_fixed
-- name    : OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:22:14.882977+00:00
-- url     : https://prove2.me/theorems/ff1c9928-56ae-4cab-848a-40fd74612ea6
-- title:
--   Extracting a block from a concatenation of equal-width blocks
-- statement:
--   Let $X_0,\dots,X_{n-1}$ be lists all of length $B$, and $X_0X_1\cdots X_{n-1}$ their concatenation. Then for every $i<n$,
--   $$
--   \bigl(X_0X_1\cdots X_{n-1}\bigr)[iB,\ iB+B)=X_i ,
--   $$
--   where $w[s,s+B)$ drops the first $s$ letters of $w$ and keeps the next $B$.
--
--   The $i$-th window of width $B$ is exactly the $i$-th block.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/BlockExtraction.lean#L22-L41

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BlockExtraction

theorem OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed {α : Type*} (blocks : List (List α)) (B : ℕ)
    (hB : ∀ z ∈ blocks, z.length = B) (i : ℕ) (hi : i < blocks.length) :
    (blocks.flatten.drop (i * B)).take B = blocks[i] := by sorry
