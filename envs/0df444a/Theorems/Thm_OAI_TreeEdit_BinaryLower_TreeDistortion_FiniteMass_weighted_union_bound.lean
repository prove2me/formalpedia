-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_union_bound
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:26:58.021983+00:00
-- url     : https://prove2.me/theorems/fb744a22-f155-4e13-9e0b-c8932f6f7bd6
-- title:
--   Union bound for weighted bad sets
-- statement:
--   Let $\iota,\nu$ be finite, $H\ge0$ on $\iota$, and $\mathrm{bad}(v,i)$ a family of predicates. Then
--   $$
--   \sum_{i:\ \exists v,\ \mathrm{bad}(v,i)}H_i\le\sum_v\ \sum_{i:\ \mathrm{bad}(v,i)}H_i .
--   $$
--
--   The mass of a union is at most the sum of the masses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L116-L139

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound {ι ν : Type*} [Fintype ι] [Fintype ν]
    (H : ι → ℝ) (bad : ν → ι → Prop) (hH : ∀ i, 0 ≤ H i) :
    (∑ i, if ∃ v, bad v i then H i else 0) ≤
      ∑ v, ∑ i, if bad v i then H i else 0 := by sorry
