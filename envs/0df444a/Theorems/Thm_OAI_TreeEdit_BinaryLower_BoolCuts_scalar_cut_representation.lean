-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_BoolCuts_scalar_cut_representation
-- name    : OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:42:51.572929+00:00
-- url     : https://prove2.me/theorems/28736bf9-2f45-4965-98cd-81ef5750db49
-- title:
--   Cut decomposition of a real function on a finite set
-- statement:
--   A cut of a finite set $S$ is a map $C:S\to\{0,1\}$ with cut distance $d_C(x,y)=|C(x)-C(y)|$; it is constant if it takes one value. For every $f:S\to\mathbb R$ on a finite set $S$ there are weights $a(C)\ge0$ on cuts, vanishing on the constant cuts, with
--   $$
--   |f(x)-f(y)|=\sum_Ca(C)\,d_C(x,y)\qquad\text{for all }x,y\in S .
--   $$
--
--   Every one-dimensional pseudometric $|f(x)-f(y)|$ lies in the cut cone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean#L114-L165

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

theorem OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation {S : Type*} [Fintype S] [DecidableEq S]
    (f : S → ℝ) :
    ∃ a : (S → Bool) → ℝ,
      (∀ C, 0 ≤ a C) ∧
      (∀ x y, |f x - f y| = ∑ C, a C * cutDistance C x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 := by sorry
