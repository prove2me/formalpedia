-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_CutAggregation_cut_mass_bound
-- name    : OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:44:02.230406+00:00
-- url     : https://prove2.me/theorems/3d5675f9-4884-493e-b3a5-609bec696466
-- title:
--   Total cut weight is bounded by total distance
-- statement:
--   Let $S$ be finite, $F:S\to\ell_1$, and $\|F(x)-F(y)\|_1=\sum_cA_c|U_c(x)-U_c(y)|$ with $A_c\ge0$. Suppose every $c$ with $A_c\ne0$ separates some pair, $|U_c(x)-U_c(y)|=1$. Then
--   $$
--   \sum_cA_c\le\frac12\sum_{(x,y)\in S\times S}\|F(x)-F(y)\|_1 .
--   $$
--
--   Each cut in use separates at least one ordered pair in each direction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CutAggregation.lean#L75-L115

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
universe u v

theorem OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound {S : Type u} {C : Type v} [Fintype S] [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (A : C → ℝ)
    (hA : ∀ c, 0 ≤ A c)
    (hcut : ∀ c, A c = 0 ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) :
    ∑ c, A c ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by sorry
