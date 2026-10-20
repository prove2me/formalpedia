-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_detection_bound
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:26:11.40713+00:00
-- url     : https://prove2.me/theorems/d20653e1-455e-40a4-a5e4-1bc4f6b6d42c
-- title:
--   Detecting bad indices by weighted tests
-- statement:
--   Let $\iota,\sigma$ be finite, $H\ge0$ on $\iota$ and $a_{s,i}\ge0$. If every bad index $i$ satisfies $\sum_sa_{s,i}\ge1$, then
--   $$
--   \sum_{i\text{ bad}}H_i\le\sum_s\sum_ia_{s,i}H_i .
--   $$
--
--   Tests that jointly detect each bad index bound its mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L95-L114

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

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (bad : ι → Prop)
    (hH : ∀ i, 0 ≤ H i) (ha : ∀ s i, 0 ≤ a s i)
    (hdetect : ∀ i, bad i → 1 ≤ ∑ s, a s i) :
    (∑ i, if bad i then H i else 0) ≤ ∑ s, ∑ i, a s i * H i := by sorry
