-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_BoolCuts_group_cuts
-- name    : OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:42:07.731387+00:00
-- url     : https://prove2.me/theorems/0cca0b81-2909-4300-b062-76f27781e52f
-- title:
--   Regrouping weighted cuts by cut function
-- statement:
--   A cut of a finite set $S$ is a map $C:S\to\{0,1\}$ with cut distance $d_C(x,y)=|C(x)-C(y)|$; it is constant if it takes one value. Let $S$ be finite, $C_i$ cuts indexed by a finite set and $w_i\ge0$. Then there are weights $a(D)\ge0$, indexed by all cuts $D$ of $S$, such that
--   $$
--   \sum_iw_i\,d_{C_i}(x,y)=\sum_Da(D)\,d_D(x,y)\quad\text{for all }x,y,
--   $$
--   and $a$ vanishes on the two constant cuts.
--
--   Repeated cuts are merged and constant cuts can be dropped.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean#L72-L112

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BoolCuts
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (C : I → S → Bool) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ a : (S → Bool) → ℝ,
      (∀ D, 0 ≤ a D) ∧
      (∀ x y, ∑ i, w i * cutDistance (C i) x y =
        ∑ D, a D * cutDistance D x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 := by sorry
