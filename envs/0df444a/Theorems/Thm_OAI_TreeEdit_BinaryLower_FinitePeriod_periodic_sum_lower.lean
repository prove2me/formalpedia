-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FinitePeriod_periodic_sum_lower
-- name    : OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:46:47.490709+00:00
-- url     : https://prove2.me/theorems/b6c5c92b-a2a6-4e72-aba2-024c0bdc9f42
-- title:
--   Long sums of a periodic function with large period sum
-- statement:
--   Let $f:\mathbb N\to[0,\infty)$ be periodic with period $q>0$ and $\sum_{s<q}f(s)=2q$. Then for every $J\ge2q$,
--   $$
--   J\le\sum_{s<J}f(s).
--   $$
--
--   A function averaging $2$ over each period sums to at least the length over any window of two periods or more.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FinitePeriod.lean#L33-L57

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

theorem OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower {f : ℕ → ℝ} {q J : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J)
    (hperiod : Function.Periodic f q) (hnonneg : ∀ s, 0 ≤ f s)
    (hcycle : ∑ s ∈ Finset.range q, f s = 2 * (q : ℝ)) :
    (J : ℝ) ≤ ∑ s ∈ Finset.range J, f s := by sorry
