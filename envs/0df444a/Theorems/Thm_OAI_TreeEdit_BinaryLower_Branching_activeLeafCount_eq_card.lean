-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Branching_activeLeafCount_eq_card
-- name    : OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:35:28.468763+00:00
-- url     : https://prove2.me/theorems/d59d7b16-b98c-467e-afc7-009729e2521a
-- title:
--   Counting active descendants by paths
-- statement:
--   Let $\mathcal A$ be a decidable predicate on lists over a finite alphabet $\alpha$, $v$ a list and $h\in\mathbb N$. The recursive count of active descendants of $v$ exactly $h$ levels below equals
--   $$
--   \bigl|\{f:\{1..h\}\to\alpha:\ \mathcal A(v\,f)\}\bigr|,
--   $$
--   the number of length-$h$ paths $f$ for which the extension $v\,f$ is active.
--
--   The recursion simply enumerates paths below $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Branching.lean#L75-L102

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Branching
variable {α : Type*} [Fintype α]

theorem OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card (A : List α → Prop) [DecidablePred A] (v : List α) (h : ℕ) :
    activeLeafCount A v h =
      (Finset.univ.filter fun f : Fin h → α => A (v ++ List.ofFn f)).card := by sorry
