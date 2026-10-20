-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_l1_bool_cut_representation
-- name    : OAI.TreeEdit.BinaryLower.l1_bool_cut_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:44:45.408086+00:00
-- url     : https://prove2.me/theorems/477d9c0b-36ac-4a62-a9e6-2464fb818b4d
-- title:
--   Cut decomposition of finite subsets of l1
-- statement:
--   A cut of a finite set $S$ is a map $C:S\to\{0,1\}$ with cut distance $d_C(x,y)=|C(x)-C(y)|$; it is constant if it takes one value. For every map $F:S\to\ell_1$ from a finite set there are weights $a(C)\ge0$ on cuts of $S$, vanishing on constant cuts, with
--   $$
--   \|F(x)-F(y)\|_1=\sum_Ca(C)\,d_C(x,y)\quad\text{and}\quad\sum_Ca(C)\le\frac12\sum_{x,y}\|F(x)-F(y)\|_1 .
--   $$
--
--   Finite subsets of $\ell_1$ are exactly the nonnegative combinations of cut pseudometrics.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteDisplacement.lean#L26-L72

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.l1_bool_cut_representation {S : Type*} [Fintype S] [DecidableEq S]
    (F : S → RealL1) :
    ∃ a : (S → Bool) → ℝ, (∀ C, 0 ≤ a C) ∧
      (∀ x y, ‖F x - F y‖ = ∑ C, a C * BoolCuts.cutDistance C x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 ∧
      (∑ C, a C) ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by sorry
