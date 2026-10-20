-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_CutAggregation_aggregate
-- name    : OAI.TreeEdit.BinaryLower.CutAggregation.aggregate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:43:30.522368+00:00
-- url     : https://prove2.me/theorems/c0fddfd1-026d-4d5d-b258-f2fffa3bee02
-- title:
--   Aggregating coordinatewise cut weights of an l1 map
-- statement:
--   Let $S$ be a set, $F:S\to\ell_1$, and $U_c:S\to\mathbb R$ indexed by a finite set. Suppose each coordinate $n$ has weights $a_n(c)\ge0$ with
--   $$
--   |F(x)_n-F(y)_n|=\sum_ca_n(c)\,|U_c(x)-U_c(y)| .
--   $$
--   Suppose also that each $c$ either has all $a_n(c)=0$ or satisfies $|U_c(x)-U_c(y)|=1$ for some pair. Then $A_c=\sum_na_n(c)$ converges, and $\|F(x)-F(y)\|_1=\sum_cA_c|U_c(x)-U_c(y)|$.
--
--   The coordinate expansions add up to one expansion of the $\ell_1$ distance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CutAggregation.lean#L42-L73

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

theorem OAI.TreeEdit.BinaryLower.CutAggregation.aggregate {S : Type u} {C : Type v} [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (a : ℕ → C → ℝ)
    (ha : ∀ n c, 0 ≤ a n c)
    (hcut : ∀ c, (∀ n, a n c = 0) ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ n x y,
      |F x n - F y n| = ∑ c, a n c * |U c x - U c y|) :
    ∃ A : C → ℝ, (∀ c, 0 ≤ A c) ∧
      (∀ c, A c = ∑' n, a n c) ∧
      (∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) := by sorry
